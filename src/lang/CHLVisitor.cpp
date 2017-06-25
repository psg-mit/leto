#include <cstdio>
#include <cstring>

#include "CHLVisitor.h"

#define BUF_SIZE 16
#define Z3_BIN "z3 -smt2 /tmp/constraints.smt2"
#define Z3_TMP "/tmp/constraints.smt2"

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wexit-time-destructors"
#pragma clang diagnostic ignored "-Wglobal-constructors"
static std::vector<z3::expr*> IGNORE_1D = {nullptr};
static std::vector<z3::expr*> IGNORE_2D = {nullptr, nullptr};
static const std::string H_TMP_PREFIX = "h-tmp-";
#pragma clang diagnostic pop

static const int EXIT_RUNTIME_ERROR = 2;


namespace lang {

  CHLVisitor::CHLVisitor(z3::context* context_,
                         z3::solver* solver_,
                         model::Z3Visitor* model_visitor_,
                         std::ofstream& z3_log_,
                         std::ofstream& smt2_log_) : context(context_),
                                                     z3_log(z3_log_),
                                                     smt2_log(smt2_log_) {
    //z3::set_param("verbose", 10);
    solver = solver_;
    model_visitor = model_visitor_;
    in_assign = false;
    errors = 0;
    while_count = 0;
    ignore_original = ignore_relaxed = 0;
    unsat_context = false;
    unknown_context = false;
    in_houdini = false;
    forall_i = new z3::expr(this->context->int_const("forall_i"));
    forall_j = new z3::expr(this->context->int_const("forall_j"));
    forall_ctr = 0;
    constraints_generated = 0;
    z3_model = nullptr;
    houdini_failed = false;
    h_tmp = 0;
    passed_houdini_pre = false;
    cur_houdini_vars = nullptr;
    inner_h_unknown = false;
  }

  static z3::check_result z3_bin(const std::string& constraints,
                                 bool add_check_sat) {
    int res;

    // Write constraints to temp file
    std::ofstream tmp(Z3_TMP, std::ios_base::trunc);
    tmp << constraints << std::endl;
    if (add_check_sat) tmp << "(check-sat)" << std::endl;

    // Start Z3 process
    FILE* stdio = popen(Z3_BIN, "r");
    assert(stdio);

    // Read result
    char buf[BUF_SIZE] = {0};
    size_t read = fread(buf, 1, BUF_SIZE, stdio);
    assert(read);
    assert(feof(stdio));

    // End Z3 process
    res = pclose(stdio);
    assert(res != -1);

    // Close temp file
    tmp.close();

    if (strncmp(buf, "sat\n", BUF_SIZE) == 0) return z3::sat;
    else if (strncmp(buf, "unsat\n", BUF_SIZE) == 0) return z3::unsat;
    else if (strncmp(buf, "unknown\n", BUF_SIZE) == 0) return z3::unknown;

    assert(false);
  }

  static void debug_print(const std::string &str) {
#ifndef NDEBUG
    std::cout << str << std::endl;
#endif
  }

  static void star_line() {
    debug_print("***********************************************************");
  }

  void CHLVisitor::push_prefix(z3::expr* prefix) {
    prefixes.push_back(prefix);
  }

  void CHLVisitor::pop_prefix() {
    assert(!prefixes.empty());
    prefixes.pop_back();
  }

  z3::expr* CHLVisitor::get_current_var(std::string name) {
    unsigned version = var_version.at(name);
    name += "-" + std::to_string(version);
    return vars.at(name);
  }

  z3::func_decl* CHLVisitor::get_current_vec(std::string name) {
    unsigned version = var_version.at(name);
    name += "-" + std::to_string(version);
    return vectors.at(name);
  }

  z3::expr* CHLVisitor::get_previous_var(std::string name) {
    unsigned version = var_version.at(name);
    assert(version);
    --version;
    name += "-" + std::to_string(version);
    return vars.at(name);
  }

  bool CHLVisitor::contains_var(std::string name) {
    if (!var_version.count(name)) return false;
    unsigned version = var_version.at(name);
    name += "-" + std::to_string(version);
    return vars.count(name);
  }

  z3::expr CHLVisitor::get_constraint(const z3::expr& constraint,
                                      bool invert_last) {
    if (prefixes.empty()) {
      return constraint;
    } else {
      std::vector<z3::expr*>::reverse_iterator rit = prefixes.rbegin();
      z3::expr impl = constraint;
      if (invert_last) {
        impl = z3::implies(!(**rit), constraint);
      } else {
        impl = z3::implies(**rit, constraint);
      }
      ++rit;
      for (; rit != prefixes.rend(); ++rit) impl = z3::implies(**rit, impl);
      return impl;
    }
  }

  void CHLVisitor::add_constraint(const z3::expr& constraint,
                                  bool invert_last) {
    ++constraints_generated;
    solver->add(get_constraint(constraint, invert_last));
  }

  void CHLVisitor::add_checked_constraint(const z3::expr& constraint) {
    ++constraints_generated;
    check_context();
    solver->add(!get_constraint(constraint, false));
  }

  void CHLVisitor::check_context() {
#ifndef NO_CHECK_CONTEXT
    std::cout << "Checking context for satisfiability" << std::endl;
    z3::check_result res = check(false);
    switch (res) {
      case z3::sat:
        break;
      case z3::unknown:
        std::cerr << "WARNING: Context is unknown" << std::endl;
        unknown_context = true;
        break;
      case z3::unsat:
        std::cerr << "WARNING: Context is unsatisfiable" << std::endl;
        unsat_context = true;
        break;
    }
#endif
  }


  z3::expr* CHLVisitor::make_float(const std::string& name) {
    Z3_sort fl = Z3_mk_fpa_sort_single(*context);
    Z3_symbol sym = Z3_mk_string_symbol(*context, name.c_str());
    Z3_ast var = Z3_mk_const(*context, sym, fl);
    return new z3::expr(z3::to_expr(*context, var));
  }

  z3pair CHLVisitor::add_var(type_t type,
                             std::string oname,
                             std::string rname) {
    unsigned version = 0;
    if (var_version.count(oname)) {
      assert(var_version.at(oname) == var_version.at(rname));
      version = var_version.at(oname) + 1;
    }

    var_version[oname] = version;
    var_version[rname] = version;
    oname += "-" + std::to_string(version);
    rname += "-" + std::to_string(version);
    z3::expr *oexpr = nullptr;
    z3::expr *rexpr = nullptr;
    switch (type) {
      case INT:
        oexpr = new z3::expr(this->context->int_const(oname.c_str()));
        rexpr = new z3::expr(this->context->int_const(rname.c_str()));
        break;
      case REAL:
        oexpr = new z3::expr(this->context->real_const(oname.c_str()));
        rexpr = new z3::expr(this->context->real_const(rname.c_str()));
        break;
      case FLOAT:
        oexpr = make_float(oname);
        rexpr = make_float(rname);
        break;
      case BOOL:
        oexpr = new z3::expr(this->context->bool_const(oname.c_str()));
        rexpr = new z3::expr(this->context->bool_const(rname.c_str()));
        break;
    }

    assert(oexpr);
    assert(rexpr);

    vars[oname] = oexpr;
    vars[rname] = rexpr;

    return {oexpr, rexpr};
  }

  z3::expr* CHLVisitor::vector_equals(z3::func_decl& x,
                                      z3::func_decl& y,
                                      const std::vector<z3::expr*>& dimensions,
                                      std::vector<z3::expr*>& ignore_index) {
    assert(ignore_index.size() == dimensions.size());

    z3::expr *ret = nullptr;
    switch (dimensions.size()) {
      case 1:
        {
          z3::expr bounds = (*forall_i >= context->int_val(0)) &&
                            (*forall_i < *dimensions.at(0));
          z3::expr eq = z3::implies(bounds, (x(*forall_i) == y(*forall_i)));
          if (ignore_index.at(0)) {
            z3::expr cond = *forall_i != *ignore_index.at(0);
            ret = new z3::expr(z3::forall(*forall_i, z3::implies(cond, eq)));
          } else {
            ret = new z3::expr(z3::forall(*forall_i, eq));
          }
        }
        break;
      case 2:
        {
          z3::expr* ignore_i = ignore_index.at(0);
          z3::expr* ignore_j = ignore_index.at(1);
          assert((ignore_i && ignore_j) || (!ignore_i && !ignore_j));


          z3::expr bounds = (*forall_i >= context->int_val(0)) &&
                            (*forall_i < *dimensions.at(0)) &&
                            (*forall_j >= context->int_val(0)) &&
                            (*forall_j < *dimensions.at(1));
          z3::expr eq = (x(*forall_i, *forall_j) == y(*forall_i, *forall_j));
          if (ignore_i) {
            z3::expr cond = !(*forall_i != *ignore_i &&
                              *forall_j != *ignore_j);
            ret = new z3::expr(z3::forall(*forall_i,
                                          *forall_j,
                                          z3::implies(cond, eq)));
          } else {
            ret = new z3::expr(z3::forall(*forall_i, *forall_j, eq));
          }
        }
        break;
      default:
        assert(false);
    }

    assert(ret);
    return ret;
  }

  vec_pair CHLVisitor::add_vector(type_t type,
                                  const std::string& oname,
                                  const std::string& rname,
                                  const std::vector<z3::expr*>& dimensions) {
    z3::func_decl* ofun = nullptr;
    z3::func_decl* rfun = nullptr;
    z3::sort is = context->int_sort();
    z3::sort rs = context->real_sort();
    z3::sort fs = z3::sort(*context, Z3_mk_fpa_sort_single(*context));
    switch (dimensions.size()) {
      case 1:
        switch (type) {
          case INT:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             is));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             is));
            break;
          case REAL:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             rs));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             rs));
            break;
          case FLOAT:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             fs));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             fs));
            break;
          case BOOL:
            assert(false);
            break;
        }
        break;
      case 2:
        switch (type) {
          case INT:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             is,
                                                             is));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             is,
                                                             is));
            break;
          case REAL:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             is,
                                                             rs));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             is,
                                                             rs));
            break;
          case FLOAT:
            ofun = new z3::func_decl(this->context->function(oname.c_str(),
                                                             is,
                                                             is,
                                                             fs));
            rfun = new z3::func_decl(this->context->function(rname.c_str(),
                                                             is,
                                                             is,
                                                             fs));
            break;
          case BOOL:
            assert(false);
            break;
        }
        break;
      default:
        assert(false);
        break;
    }

    assert(ofun);
    assert(rfun);

    vectors[oname] = ofun;
    vectors[rname] = rfun;

    return {ofun, rfun};
  }


  z3pair CHLVisitor::visit(Declare &node) {
    for (VarList* head = node.vars; head; head = head->cdr) {
      Var* var = head->car;

      // Declare var<o> and var<r>
      std::string oname = var->name + "<o>";
      std::string rname = var->name + "<r>";

      z3pair res = add_var(node.type, oname, rname);

      types[var->name] = node.type;
      if (node.specvar) specvars.insert(var->name);

      // Assume variables are equal at declare time
      add_constraint(*res.original == *res.relaxed);
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(DeclareMat &node) {
    for (VarList* head = node.vars; head; head = head->cdr) {
      Var* var = head->car;

      // Declare var<o> and var<r>
      std::string oname = var->name + "<o>";
      std::string rname = var->name + "<r>";
      var_version[oname] = 0;
      var_version[rname] = 0;
      oname += "-0";
      rname += "-0";

      // Build dimension vector
      std::vector<z3::expr*>* dimensions = new std::vector<z3::expr*>();
      for (RelationalExp* expr : head->dimensions) {
        assert(expr);
        z3pair res = expr->accept(*this);
        assert(res.original);
        assert(!res.relaxed);
        dimensions->push_back(res.original);
      }

      vec_pair res = add_vector(node.type, oname, rname, *dimensions);

      types[var->name] = node.type;
      dim_map[var->name] = dimensions;

      if (node.specvar) specvars.insert(var->name);

      // Assume vectors are equal at declare time
      z3::expr* eq = vector_equals(*res.original,
                                   *res.relaxed,
                                   *dimensions,
                                   dimensions->size() == 1 ? IGNORE_1D : IGNORE_2D);

      add_constraint(*eq);
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(DeclareLMat &node) {
    // Record that this is a light matrix
    light_mats.insert(node.var->name);

    // Save type info for whole fake matrix in case of ArrayAssign
    types[node.var->name] = node.type;

    // Save dimension as well
    light_dim_map[node.var->name] = &node.dimensions;


    // Loop through dimensions declaring vars for each possible entry
    switch (node.dimensions.size()) {
      case 1:
        for (int i = 0; i < node.dimensions.at(0); ++i) {
          std::string base = node.var->name + "-" + std::to_string(i);
          std::string oname = base + "<o>";
          std::string rname = base + "<r>";

          add_var(node.type, oname, rname);
          types[base] = node.type;
        }
        break;
      case 2:
        for (int i = 0; i < node.dimensions.at(0); ++i) {
          for (int j = 0; j < node.dimensions.at(1); ++j) {
            std::string base = node.var->name +
                               "-" +
                               std::to_string(i) +
                               "-" +
                               std::to_string(j);
            std::string oname = base + "<o>";
            std::string rname = base + "<r>";

            add_var(node.type, oname, rname);
            types[base] = node.type;
          }
        }
        break;
      default:
        assert(false);
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(StatementList &node) {
    node.lhs->accept(*this);
    node.rhs->accept(*this);

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(ArrayAssign &node) {
    // Fill virtual vector
    virtual_vec.clear();
    node.rhs->accept(*this);

    last_dim = nullptr;
    last_light_dim = nullptr;
    last_base_name = nullptr;
    node.lhs->accept(*this);
    assert((last_dim != nullptr) ^ (last_light_dim != nullptr));
    assert(last_base_name);

    if (light_mats.count(*last_base_name)) {
      // Construct normal assign nodes
      std::string base_name = *last_base_name;
      switch (last_light_dim->size()) {
        case 1:
          assert(virtual_vec.size() == static_cast<size_t>(last_light_dim->at(0)));
          for (int i = 0; i < last_light_dim->at(0); ++i) {
            // Build left hand side
            std::string name = base_name + "-" + std::to_string(i);
            Var lhs(name);

            // Build assignment
            Assign virtual_assign(&lhs, virtual_vec.at(static_cast<size_t>(i)));

            // Eval fake assign
            virtual_assign.accept(*this);
          }
          break;
        case 2:
          assert(virtual_vec.size() == static_cast<size_t>(last_light_dim->at(0) *
                                                           last_light_dim->at(1)));
          for (int i = 0; i < last_light_dim->at(0); ++i) {
            for (int j = 0; j < last_light_dim->at(1); ++j) {
              // Build left hand side
              std::string name = base_name +
                                 "-" +
                                 std::to_string(i) +
                                 "-" +
                                 std::to_string(j);
              Var lhs(name);

              // Build assignment
              Expression* rhs = virtual_vec.at(static_cast<size_t>(i *
                                                                   last_light_dim->at(1) +
                                                                   j));
              Assign virtual_assign(&lhs, rhs);

              // Eval fake assign
              virtual_assign.accept(*this);
            }
          }
          break;
        default:
          assert(false);
      }

      return {nullptr, nullptr};
    }

    // Prep new vectors
    std::string oname = *last_base_name + "<o>";
    std::string rname = *last_base_name + "<r>";
    unsigned version = var_version.at(oname);
    assert(version == var_version.at(rname));
    ++version;
    ++var_version.at(oname);
    ++var_version.at(rname);
    oname += "-" + std::to_string(version);
    rname += "-" + std::to_string(version);
    add_vector(types.at(*last_base_name), oname, rname, *last_dim);
    last_array = {vectors.at(oname), vectors.at(rname)};


    // Fill from virtual vector
    switch (last_dim->size()) {
      case 1:
        for (size_t i = 0; i < virtual_vec.size(); ++i) {
          // Eval vec at i
          z3pair constraint = virtual_vec.at(i)->accept(*this);
          add_constraint((*last_array.original)
                             (context->int_val(static_cast<int>(i))) == *constraint.original);
          add_constraint((*last_array.relaxed)
                             (context->int_val(static_cast<int>(i))) == *constraint.relaxed);
        }
        break;
      case 2:
        // TODO: Figure out virtual vectors for multidimensional dynamic arrays
        assert(false);
        /*
        assert(virtual_vec.size() == static_cast<size_t>(last_dim->at(0) *
                                                         last_dim->at(1)));
        for (int i = 0; i < last_dim->at(0); ++i) {
          for (int j = 0; j < last_dim->at(1); ++j) {
            // Eval vec at i, j
            z3pair constraint = virtual_vec.at(static_cast<size_t>(i * last_dim->at(1) + j))->accept(*this);
            add_constraint((*last_array.original)
                               (context->int_val(i),
                                context->int_val(j)) == *constraint.original);
            add_constraint((*last_array.relaxed)
                               (context->int_val(i),
                                context->int_val(j)) == *constraint.relaxed);
          }
        }
        */
        break;
      default:
        assert(false);
    }

    return {nullptr, nullptr};
  }

  // FIXME: Replacement only happens in assignments.  Is this bad?  Not sure!
  // On one hand, it means assertions are always reliable, but on the other
  // hand expressions in conditionals are too.  Perhaps something more fine
  // grained is needed here
  z3pair CHLVisitor::visit(Assign &node) {
    // Check for <array> = <array>
    Var* vlhs = dynamic_cast<Var*>(node.lhs);
    if (vlhs && (light_mats.count(vlhs->name) || dim_map.count(vlhs->name))) {
      // Replace this assignment with a Copy node
      Var* vrhs = dynamic_cast<Var*>(node.rhs);
      assert(vrhs);

      Copy array_copy(vrhs, vlhs);
      return array_copy.accept(*this);
    }

    model_visitor->unprep();
    // If prepped, replace op.  Else do what we do now
    // Get both pairs
    z3pair rhs = node.rhs->accept(*this);
    in_assign = true;
    z3pair lhs = node.lhs->accept(*this);
    in_assign = false;

    assert(old_o);
    assert(old_r);

    // Both executions should have expressions
    assert(lhs.original);
    assert(lhs.relaxed);
    assert(rhs.original);
    assert(rhs.relaxed);

    z3::expr *ores = nullptr;
    if (!ignore_original) {
      // Set LHS<o> == RHS<o>
      ores = new z3::expr(*lhs.original == *rhs.original);
    } else {
      // Set LHS<o> == LHS<o>-prev
      ores = new z3::expr(*lhs.original == *old_o);
    }
    assert(ores);
    add_constraint(*ores);
    if (!prefixes.empty()) add_constraint(*lhs.original == *old_o, true);

    // Set LHS<r> == RHS<r>
    z3::expr *rres = nullptr;
    if (!ignore_relaxed) {
      if (model_visitor->prepped()) {
        rres = model_visitor->replace_op(expr_type, lhs.relaxed);
        if (!prefixes.empty()) {
          for (const std::string& var : *model_visitor->updated) {
            z3::expr* cur = model_visitor->get_current_var(var);
            z3::expr* prev = model_visitor->get_previous_var(var);
            add_constraint(*cur == *prev, true);
          }
        }
      } else {
        rres = new z3::expr(*lhs.relaxed == *rhs.relaxed);
      }
    } else {
      rres = new z3::expr(*lhs.relaxed == *old_r);
    }
    assert(rres);
    add_constraint(*rres);
    if (!prefixes.empty()) add_constraint(*lhs.relaxed == *old_r, true);

    return {ores, rres};
  }

  z3pair CHLVisitor::visit(Var &node) {
    // Unversioned var names
    last_base_name = &node.name;
    std::string oname = node.name + "<o>";
    std::string rname = node.name + "<r>";
    z3::expr* oexpr = nullptr;
    z3::expr* rexpr = nullptr;
    expr_type = types.at(node.name);
    if (in_assign) {
      old_o = old_r = nullptr;
      // Get old version
      old_o = get_current_var(oname);
      old_r = get_current_var(rname);

      // Rev version number
      unsigned version = ++var_version.at(oname);
      assert(version);
      ++var_version.at(rname);
      assert(var_version.at(oname) == var_version.at(rname));

      // Construct new variables
      oname += "-" + std::to_string(version);
      rname += "-" + std::to_string(version);
      switch (expr_type) {
        case INT:
          oexpr = new z3::expr(this->context->int_const(oname.c_str()));
          rexpr = new z3::expr(this->context->int_const(rname.c_str()));
          break;
        case REAL:
          oexpr = new z3::expr(this->context->real_const(oname.c_str()));
          rexpr = new z3::expr(this->context->real_const(rname.c_str()));
          break;
        case FLOAT:
          oexpr = make_float(oname);
          rexpr = make_float(rname);
          break;
        case BOOL:
          oexpr = new z3::expr(this->context->bool_const(oname.c_str()));
          rexpr = new z3::expr(this->context->bool_const(rname.c_str()));
          break;
      }

      vars[oname] = oexpr;
      vars[rname] = rexpr;

      assert(old_o);
      assert(old_r);
    } else {
      bool is_light_mat = light_mats.count(node.name);
      if (is_light_mat || !contains_var(oname)) {
        // Working with undereferenced array, do backchannel return
        if (is_light_mat) {
          last_light_dim = light_dim_map.at(node.name);
        } else {
          last_array = {get_current_vec(oname), get_current_vec(rname)};
          last_dim = dim_map.at(node.name);
        }
        return {nullptr, nullptr};
      }

      unsigned version = var_version.at(oname);
      assert(version == var_version.at(rname));

      oexpr = vars.at(oname + "-" + std::to_string(version));
      rexpr = vars.at(rname + "-" + std::to_string(version));
    }

    assert(oexpr);
    assert(rexpr);
    return {oexpr, rexpr};
  }

  z3pair CHLVisitor::visit(ExprList &node) {
    // Fill virtual array
    virtual_vec.push_back(node.car);

    if (node.cdr) {
      // Continue to rest of list
      node.cdr->accept(*this);
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(BinOp &node) {
    // TODO: This will NOT work for chains of binary operators because of how
    // model::OperatorVisitor works

    // Get both pairs
    z3pair lhs = node.lhs->accept(*this);
    type_t lhs_type = expr_type;
    z3pair rhs = node.rhs->accept(*this);
    assert (lhs_type == REAL || lhs_type == INT);
    assert (expr_type == REAL || expr_type == INT);
    // TODO: can't mix ints and reals in division (Z3 sometimes casts things to
    // ints and messes it all up)
    assert ((node.op != RDIV && node.op != ODIV) || expr_type == lhs_type);
    expr_type = lhs_type == REAL || expr_type == REAL ? REAL : INT;

    model_visitor->prep_op(node.op, lhs.relaxed, rhs.relaxed);

    // Both executions should have expressions
    assert(lhs.original);
    assert(lhs.relaxed);
    assert(rhs.original);
    assert(rhs.relaxed);

    // Build relational pairs
    z3::expr *ores = binop(context, node.op, expr_type, lhs.original, rhs.original);
    z3::expr *rres = binop(context, node.op, expr_type, lhs.relaxed, rhs.relaxed);

    assert(ores);
    assert(rres);
    return {ores, rres};
  }

  z3pair CHLVisitor::visit(FaultyRead &node) {
    z3pair var = node.var->accept(*this);
    assert(var.original);
    assert(var.relaxed);

    model_visitor->prep_op(FREAD, var.relaxed, nullptr);
    return var;
  }

  z3pair CHLVisitor::visit(FaultyWrite &node) {
    assert(!in_assign);
    in_assign = true;
    z3pair dest = node.dest->accept(*this);
    in_assign = false;
    z3pair val = node.val->accept(*this);

    assert(dest.original);
    assert(dest.relaxed);
    assert(val.original);
    assert(val.relaxed);

    if (!ignore_relaxed) {
      model_visitor->prep_op(FWRITE, dest.relaxed, val.relaxed);
      z3::expr* res = model_visitor->replace_op(expr_type, nullptr);
      add_constraint(*res);
    }

    if (!ignore_original) {
      z3::expr res = (*dest.original == *val.original);
      add_constraint(res);
    }

    return {nullptr, nullptr};
  }

  // TODO: Make this work for light matrices
  z3pair CHLVisitor::visit(BoolExp &node) {
    // Prepare for dimension info
    last_dim = nullptr;
    last_light_dim = nullptr;

    // Get both pairs
    last_array = {nullptr, nullptr};
    z3pair lhs = node.lhs->accept(*this);
    vec_pair lhs_array = last_array;
    type_t lhs_type = expr_type;
    last_array = {nullptr, nullptr};
    z3pair rhs = node.rhs->accept(*this);
    vec_pair rhs_array = last_array;

    switch (node.op) {
      case AND:
      case OR:
      case XOR:
        lhs_array.original = lhs_array.relaxed = nullptr;
        rhs_array.original = rhs_array.relaxed = nullptr;
        break;
      case EQUALS:
      case NEQ:
      case LT:
      case LTEQ:
      case IMPLIES:
        break;
    }

    assert((lhs_array.original &&
            lhs_array.relaxed &&
            rhs_array.original &&
            rhs_array.relaxed) ||
           (!lhs_array.original &&
            !lhs_array.relaxed &&
            !rhs_array.original &&
            !rhs_array.relaxed));

    assert(!last_light_dim);

    // if lhs_array.original, deal with arrays
    z3::expr *ores = nullptr;
    z3::expr *rres = nullptr;
    if (lhs_array.original) {
      switch (node.op) {
        case EQUALS:
          switch (last_dim->size()) {
            case 1:
              ores = vector_equals(*lhs_array.original,
                                   *rhs_array.original,
                                   *last_dim,
                                   IGNORE_1D);
              rres = vector_equals(*lhs_array.relaxed,
                                   *rhs_array.relaxed,
                                   *last_dim,
                                   IGNORE_1D);
              break;
            case 2:
              ores = vector_equals(*lhs_array.original,
                                   *rhs_array.original,
                                   *last_dim,
                                   IGNORE_2D);
              rres = vector_equals(*lhs_array.relaxed,
                                   *rhs_array.relaxed,
                                   *last_dim,
                                   IGNORE_2D);
              break;
            default:
              assert(false);
          }
          return {ores, rres};
        case NEQ:
          // Run as EQ then negate
          switch (last_dim->size()) {
            case 1:
              ores = vector_equals(*lhs_array.original,
                                   *rhs_array.original,
                                   *last_dim,
                                   IGNORE_1D);
              rres = vector_equals(*lhs_array.relaxed,
                                   *rhs_array.relaxed,
                                   *last_dim,
                                   IGNORE_1D);
              break;
            case 2:
              ores = vector_equals(*lhs_array.original,
                                   *rhs_array.original,
                                   *last_dim,
                                   IGNORE_2D);
              rres = vector_equals(*lhs_array.relaxed,
                                   *rhs_array.relaxed,
                                   *last_dim,
                                   IGNORE_2D);
              break;
            default:
              assert(false);
          }
          *ores = !*ores;
          *rres = !*rres;
          expr_type = BOOL;
          return {ores, rres};

        case LT:
        case LTEQ:
        case AND:
        case OR:
        case XOR:
        case IMPLIES:
          assert(false);
      }
    }

    // Both executions should have expressions
    assert(lhs.original);
    assert(lhs.relaxed);
    assert(rhs.original);
    assert(rhs.relaxed);

    // Build relational pairs
    switch (node.op) {
      case EQUALS:
        ores = new z3::expr(*lhs.original == *rhs.original);
        rres = new z3::expr(*lhs.relaxed == *rhs.relaxed);
        break;
      case LT:
        switch (lhs_type) {
          case INT:
          case REAL:
            ores = new z3::expr(*lhs.original < *rhs.original);
            rres = new z3::expr(*lhs.relaxed < *rhs.relaxed);
            break;
          case FLOAT:
            {
              Z3_ast oast = Z3_mk_fpa_lt(*context,
                                         *lhs.original,
                                         *rhs.original);
              Z3_ast rast = Z3_mk_fpa_lt(*context, *lhs.relaxed, *rhs.relaxed);
              ores = new z3::expr(z3::to_expr(*context, oast));
              rres = new z3::expr(z3::to_expr(*context, rast));
            }
            break;
          case BOOL:
            assert(false);
            break;
        }
        break;
      case LTEQ:
        switch (lhs_type) {
          case INT:
          case REAL:
            ores = new z3::expr(*lhs.original <= *rhs.original);
            rres = new z3::expr(*lhs.relaxed <= *rhs.relaxed);
            break;
          case FLOAT:
          case BOOL:
            assert(false);
            break;
        }
        break;
      case NEQ:
        ores = new z3::expr(*lhs.original != *rhs.original);
        rres = new z3::expr(*lhs.relaxed != *rhs.relaxed);
        break;
      case AND:
        ores = new z3::expr(*lhs.original && *rhs.original);
        rres = new z3::expr(*lhs.relaxed && *rhs.relaxed);
        break;
      case OR:
        ores = new z3::expr(*lhs.original || *rhs.original);
        rres = new z3::expr(*lhs.relaxed || *rhs.relaxed);
        break;
      case IMPLIES:
        ores = new z3::expr(z3::implies(*lhs.original, *rhs.original));
        rres = new z3::expr(z3::implies(*lhs.relaxed, *rhs.relaxed));
        break;
      case XOR:
        assert(false);
        break;
    }

    expr_type = BOOL;

    assert(ores);
    assert(rres);
    return {ores, rres};
  }

  z3pair CHLVisitor::visit(RelationalVar &node) {
    if (node.check_spec && specvars.count(node.var->name)) {
      fprintf(stderr,
              "ERROR: %s is a specification variable\n",
              node.var->name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }
    last_base_name = &node.var->name;
    expr_type = types.at(node.var->name);
    std::string name;
    switch (node.relation) {
      case ORIGINAL:
        name = node.var->name + "<o>";
        break;
      case RELAXED:
        name = node.var->name + "<r>";
        break;
    }

    bool is_light_mat = light_mats.count(node.var->name);
    if (!is_light_mat && contains_var(name)) {
      return {get_current_var(name), nullptr};
    }

    // Working with an undereferenced array, need to do backchannel return
    unsigned version = var_version.at(name);
    name += "-" + std::to_string(version);
    if (is_light_mat) last_light_dim = light_dim_map.at(node.var->name);
    else {
      last_array = {vectors.at(name), nullptr};
      assert(last_array.original);
      last_dim = dim_map.at(node.var->name);
    }
    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(SpecVar &node) {
    if (!specvars.count(node.var->name)) {
      fprintf(stderr,
              "ERROR: %s is not a specification variable\n",
              node.var->name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    // TODO: Allow light specmats
    assert (!light_mats.count(node.var->name));

    RelationalVar relvar(RELAXED, node.var, false);

    return relvar.accept(*this);
  }


  z3::expr* CHLVisitor::light_mat_elem_eq(Var& lhs_elem_v,
                                         Var& rhs_elem_v,
                                         RelationalVar& lhs_rv,
                                         RelationalVar& rhs_rv) {
    // Build Relational Vars
    RelationalVar lhs_elem_rv(lhs_rv.relation, &lhs_elem_v);
    RelationalVar rhs_elem_rv(rhs_rv.relation, &rhs_elem_v);

    // Build Relational Boolean Expression
    RelationalBoolExp exp(EQUALS, &lhs_elem_rv, &rhs_elem_rv);

    // Eval
    z3pair res = exp.accept(*this);
    assert(res.original);
    assert(!res.relaxed);

    return res.original;
  }

  z3pair CHLVisitor::visit(RelationalBoolExp &node) {
    // Check for light matrices first
    RelationalVar* lhs_rv = dynamic_cast<RelationalVar*>(node.lhs);
    if (lhs_rv && light_mats.count(lhs_rv->var->name)) {
      z3::expr* ret = nullptr;
      RelationalVar* rhs_rv = dynamic_cast<RelationalVar*>(node.rhs);
      const std::string& lhs_name = lhs_rv->var->name;
      const std::string& rhs_name = rhs_rv->var->name;
      // NOTE: Right now light matrices can only be compared to other light
      // matrices
      assert(rhs_rv);
      assert(light_mats.count(rhs_name));

      // NOTE: Only equality checking for now
      assert(node.op == EQUALS);

      const std::vector<int>* lhs_dims = light_dim_map.at(lhs_name);
      const std::vector<int>* rhs_dims = light_dim_map.at(rhs_name);
      assert(lhs_dims->size() == rhs_dims->size());
      assert(*lhs_dims == *rhs_dims);
      switch (lhs_dims->size()) {
        case 1:
          {
            // Build first vars

            Var lhs_elem_v(lhs_name + "-0");
            Var rhs_elem_v(rhs_name + "-0");

            ret = light_mat_elem_eq(lhs_elem_v, rhs_elem_v, *lhs_rv, *rhs_rv);
          }
          for (int i = 1; i < lhs_dims->at(0); ++i) {
            std::string post = "-" + std::to_string(i);
            Var lhs_elem_v(lhs_name + post);
            Var rhs_elem_v(rhs_name + post);

            z3::expr* res = light_mat_elem_eq(lhs_elem_v,
                                              rhs_elem_v,
                                              *lhs_rv,
                                              *rhs_rv);

            *ret = *ret && *res;
            delete res;
          }
          break;
        case 2:
          {
            // Build first vars

            Var lhs_elem_v(lhs_name + "-0-0");
            Var rhs_elem_v(rhs_name + "-0-0");

            ret = light_mat_elem_eq(lhs_elem_v, rhs_elem_v, *lhs_rv, *rhs_rv);
          }
          for (int i = 0; i < lhs_dims->at(0); ++i) {
            for (int j = (i == 0) ? 1 : 0; j < lhs_dims->at(1); ++j) {
              std::string post = "-" +
                                 std::to_string(i) +
                                 "-" +
                                 std::to_string(j);

              Var lhs_elem_v(lhs_name + post);
              Var rhs_elem_v(rhs_name + post);

              z3::expr* res = light_mat_elem_eq(lhs_elem_v,
                                                rhs_elem_v,
                                                *lhs_rv,
                                                *rhs_rv);

              *ret = *ret && *res;
              delete res;
            }
          }
          break;
        default:
          assert(false);
      }

      expr_type = BOOL;
      return {ret, nullptr};
    }


    last_array = {nullptr, nullptr};
    // Get both pairs
    z3pair lhs = node.lhs->accept(*this);
    type_t lhs_type = expr_type;
    z3::func_decl* lhs_array = last_array.original;
    last_array = {nullptr, nullptr};
    z3pair rhs = node.rhs->accept(*this);
    z3::func_decl* rhs_array = last_array.original;
    last_array = {nullptr, nullptr};

    assert((lhs_array && rhs_array) || (!lhs_array && !rhs_array));
    z3::expr *res = nullptr;
    if (lhs_array) {
      // Dealing with an array!  Set them equal with vector_equals
      assert(node.op == EQUALS);

      switch (last_dim->size()) {
        case 1:
          res = vector_equals(*lhs_array, *rhs_array, *last_dim, IGNORE_1D);
          break;
        case 2:
          res = vector_equals(*lhs_array, *rhs_array, *last_dim, IGNORE_2D);
          break;
        default:
          assert(false);
          break;
      }
    } else {
      // Only original part should exist
      assert(lhs.original);
      assert(!lhs.relaxed);
      assert(rhs.original);
      assert(!rhs.relaxed);

      // Build relational pairs
      switch (node.op) {
        case EQUALS:
          res = new z3::expr(*lhs.original == *rhs.original);
          break;
        case LT:
          switch (lhs_type) {
            case INT:
            case REAL:
              res = new z3::expr(*lhs.original < *rhs.original);
              break;
            case FLOAT:
              {
                Z3_ast ast = Z3_mk_fpa_lt(*context,
                                          *lhs.original,
                                          *rhs.original);
                res = new z3::expr(z3::to_expr(*context, ast));
              }
              break;
            case BOOL:
              assert(false);
              break;
          }
          break;
        case LTEQ:
          switch (lhs_type) {
            case INT:
            case REAL:
              res = new z3::expr(*lhs.original <= *rhs.original);
              break;
            case FLOAT:
            case BOOL:
              assert(false);
              break;
          }
          break;
        case NEQ:
          res = new z3::expr(*lhs.original != *rhs.original);
          break;
        case AND:
          res = new z3::expr(*lhs.original && *rhs.original);
          break;
        case OR:
          res = new z3::expr(*lhs.original || *rhs.original);
          break;
        case IMPLIES:
          res = new z3::expr(z3::implies(*lhs.original, *rhs.original));
          break;
        case XOR:
          assert(false);
      }
    }

    assert(res);
    expr_type = BOOL;
    return {res, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalAssume &node) {
    z3pair assumption = node.assumption->accept(*this);

    // Relational assumptions are only original
    assert(assumption.original);
    assert(!assumption.relaxed);

    solver->add(*assumption.original);
    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalAssert &node) {
    z3pair assertion = node.assertion->accept(*this);

    assert(assertion.original);
    assert(!assertion.relaxed);

    if (!in_houdini) {
      // Check assertion
      solver->push();
      add_checked_constraint(*assertion.original);
      check();
      solver->pop();
    }

    // Assertion passed!  Add to context
    add_constraint(*assertion.original);

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(Assert &node) {
    z3pair assertion = node.assertion->accept(*this);

    assert(assertion.original);
    assert(assertion.relaxed);

    if (!ignore_original) {
      // Get original assertion as an assumption
      add_constraint(*assertion.original);
    }

    if (!ignore_relaxed) {
      if (!in_houdini) {
        // Check relaxed assertion
        solver->push();
        add_checked_constraint(*assertion.relaxed);
        check();
        solver->pop();
      }

      // Assertion passed!  Get relaxed assertion as an assumption
      add_constraint(*assertion.relaxed);
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(Fail &node) {
    z3pair clause = node.clause->accept(*this);
    assert(clause.original);
    assert(clause.relaxed);

    if (!ignore_original) {
      add_constraint(!(*clause.original));
    }

    if (!ignore_relaxed) {
      add_constraint(!(*clause.relaxed));
    }

    return {nullptr, nullptr};
  }

  z3::check_result CHLVisitor::check(bool exit_on_sat) {
    // Log constraints
    std::cout << *solver << std::endl;
    z3_log << *solver << std::endl << std::endl;
    smt2_log << solver->to_smt2() << std::endl << std::endl;

    z3::check_result res = solver->check();
    std::cout << res << std::endl;

    // Clear Z3 model
    delete z3_model;
    z3_model = nullptr;

    switch (res) {
      case z3::unsat:
        break;
      case z3::sat:
        z3_model = new z3::model(solver->get_model());
        std::cout << *z3_model << std::endl;
        if(exit_on_sat) {
          ++errors;
          // TODO: Remove this
          exit(1);
        }
        break;
      case z3::unknown:
        {
          std::cout << "reason: " << solver->reason_unknown() << std::endl;

          if (in_houdini) return z3::unknown;

          // Try again with *solver output
          std::cout << "Trying again with *solver output...";
          std::cout.flush();
          std::ostringstream constraints;
          constraints << *solver;
          res = z3_bin(constraints.str(), true);
          std::cout << res << std::endl;
          switch (res) {
            case z3::unsat:
              break;
            case z3::sat:
                if (exit_on_sat) {
                  ++errors;
                  exit(1);
                }
              break;
            case z3::unknown:
              // Try again with smt2 output
              std::cout << "Trying again with smt2 output...";
              std::cout.flush();
              res = z3_bin(solver->to_smt2(), false);
              std::cout << res << std::endl;
              switch (res) {
                case z3::unsat:
                  break;
                case z3::sat:
                  if (exit_on_sat) {
                    ++errors;
                    exit(1);
                  }
                  break;
                case z3::unknown:
                  if (exit_on_sat) {
                    ++errors;
                    exit(1);
                  }
              }
          }
        }
        break;
    }
    return res;
  }

  z3pair CHLVisitor::visit(RelationalBinOp &node) {
    // TODO: Make this work for floats
    // Get both pairs
    z3pair lhs = node.lhs->accept(*this);
    type_t lhs_type = expr_type;
    z3pair rhs = node.rhs->accept(*this);
    assert (lhs_type == REAL || lhs_type == INT);
    assert (expr_type == REAL || expr_type == INT);
    // TODO: Can't mix ints and reals in division
    assert ((node.op != RDIV  && node.op != ODIV) || expr_type == lhs_type);
    expr_type = lhs_type == REAL || expr_type == REAL ? REAL : INT;

    // Only original part should exist
    assert(lhs.original);
    assert(!lhs.relaxed);
    assert(rhs.original);
    assert(!rhs.relaxed);

    // Build relational pairs
    z3::expr *res = binop(context, node.op, lhs_type, lhs.original, rhs.original);

    assert(res);
    return {res, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalInt &node) {
    z3::expr* res = new z3::expr(context->int_val(node.value));

    assert(res);
    expr_type = INT;
    return {res, nullptr};
  }

  z3pair CHLVisitor::visit(Int &node) {
    z3::expr* res = new z3::expr(context->int_val(node.value));

    assert(res);
    expr_type = INT;
    return {res, res};
  }

  z3pair CHLVisitor::visit(RelationalReal &node) {
    assert(node.denominator);
    z3::expr* res = new z3::expr(context->real_val(node.numerator,
                                                   node.denominator));

    assert(res);
    expr_type = REAL;
    return {res, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalBool &node) {
    z3::expr* res = new z3::expr(context->bool_val(node.value));

    assert(res);
    expr_type = BOOL;
    return {res, nullptr};
  }

  z3pair CHLVisitor::visit(Bool &node) {
    z3::expr* res = new z3::expr(context->bool_val(node.value));

    assert(res);
    expr_type = BOOL;
    return {res, res};
  }

  z3pair CHLVisitor::visit(Real &node) {
    assert(node.denominator);
    z3::expr* res = new z3::expr(context->real_val(node.numerator,
                                                   node.denominator));

    assert(res);
    expr_type = REAL;
    return {res, res};
  }

  z3pair CHLVisitor::visit(Float &node) {
    z3::expr* res = float_val(context, node.value);
    assert(res);
    expr_type = FLOAT;
    return {res, res};
  }

  z3pair CHLVisitor::visit(RelationalFloat &node) {
    z3::expr* res = float_val(context, node.value);
    assert(res);
    expr_type = FLOAT;
    return {res, nullptr};
  }


  z3pair CHLVisitor::visit(ArrayAccess &node) {
    if (light_mats.count(node.lhs->name)) {
      // Convert this to a variable access

      // Build up name
      std::string base = node.lhs->name;
      assert(!node.rhs.empty());
      assert(node.rhs.size() <= 2);
      for (size_t i = 0; i < node.rhs.size(); ++i) {
          Expression* exp = node.rhs.at(i);
          Int* index = dynamic_cast<Int*>(exp);
          assert(index);
          base += "-" + std::to_string(index->value);
      }

      // Construct var and proceed with it
      Var v(base);
      return v.accept(*this);
    }

    std::string oname = node.lhs->name + "<o>";
    std::string rname = node.lhs->name + "<r>";
    unsigned version = var_version.at(oname);
    assert(version == var_version.at(rname));
    oname += "-" + std::to_string(version);
    rname += "-" + std::to_string(version);
    z3::func_decl* oarray = vectors.at(oname);
    z3::func_decl* rarray = vectors.at(rname);

    // Examine index, but be careful to remove assign flag
    bool old_in_assign = in_assign;
    in_assign = false;
    z3pair i1 = node.rhs.at(0)->accept(*this);
    in_assign = old_in_assign;

    if (in_assign) {
      std::vector<z3::expr*> ignore;
      old_o = old_r = nullptr;
      type_t type = types.at(node.lhs->name);
      std::vector<z3::expr*>* dimension = dim_map.at(node.lhs->name);
      ++version;
      ++var_version.at(node.lhs->name + "<o>");
      ++var_version.at(node.lhs->name + "<r>");
      std::string new_oname = node.lhs->name + "<o>-" + std::to_string(version);
      std::string new_rname = node.lhs->name + "<r>-" + std::to_string(version);
      add_vector(type, new_oname, new_rname, *dimension);
      z3::func_decl* new_oarray = vectors.at(new_oname);
      z3::func_decl* new_rarray = vectors.at(new_rname);

      // Set the two equal except for the index to be changed
      switch (dimension->size()) {
        case 1:
          old_o = new z3::expr((*oarray)(*i1.original));
          old_r = new z3::expr((*rarray)(*i1.relaxed));
          ignore = {i1.original};
          add_constraint(*(vector_equals(*new_oarray,
                                         *oarray,
                                         *dimension,
                                         ignore)));
          ignore = {i1.relaxed};
          add_constraint(*(vector_equals(*new_rarray,
                                         *rarray,
                                         *dimension,
                                         ignore)));

          if (!prefixes.empty()) {
            // Set equal
            ignore = {nullptr};
            add_constraint(*(vector_equals(*new_oarray,
                                           *oarray,
                                           *dimension,
                                           ignore)),
                           true);
            add_constraint(*(vector_equals(*new_rarray,
                                           *rarray,
                                           *dimension,
                                           ignore)),
                           true);
          }
          break;
        case 2:
          {
            z3pair i2 = node.rhs.at(1)->accept(*this);
            assert(i2.original);
            assert(i2.relaxed);
            old_o = new z3::expr((*oarray)(*i1.original, *i2.original));
            old_r = new z3::expr((*rarray)(*i1.relaxed, *i2.relaxed));
            ignore = {i1.original, i2.original};
            add_constraint(*(vector_equals(*new_oarray,
                                           *oarray,
                                           *dimension,
                                           ignore)));
            ignore = {i1.relaxed, i2.relaxed};
            add_constraint(*(vector_equals(*new_rarray,
                                           *rarray,
                                           *dimension,
                                           ignore)));

            if (!prefixes.empty()) {
              ignore = {nullptr, nullptr};
              add_constraint(*(vector_equals(*new_oarray,
                                             *oarray,
                                             *dimension,
                                             ignore)),
                             true);
              add_constraint(*(vector_equals(*new_rarray,
                                             *rarray,
                                             *dimension,
                                             ignore)),
                             true);

            }
          }
          break;
        default:
          assert(false);
          break;
      }

      oarray = new_oarray;
      rarray = new_rarray;

      assert(old_o);
      assert(old_r);
    }

    assert(oarray);
    assert(rarray);
    assert(i1.original);
    assert(i1.relaxed);

    z3::expr* oexpr = nullptr;
    z3::expr* rexpr = nullptr;
    switch (node.rhs.size()) {
      case 1:
        oexpr = new z3::expr((*oarray)(*i1.original));
        rexpr = new z3::expr((*rarray)(*i1.relaxed));
        break;
      case 2:
        {
          z3pair i2 = node.rhs.at(1)->accept(*this);
          assert(i2.original);
          assert(i2.relaxed);
          oexpr = new z3::expr((*oarray)(*i1.original, *i2.original));
          rexpr = new z3::expr((*rarray)(*i1.relaxed, *i2.relaxed));
        }
        break;
      default:
        // TODO: Up to 5
        assert(false);
        break;
    }
    assert(oexpr);
    assert(rexpr);

    expr_type = types.at(node.lhs->name);

    return {oexpr, rexpr};
  }

  z3pair CHLVisitor::visit(RelationalArrayAccess &node) {
    if (node.check_spec && specvars.count(node.lhs->name)) {
      fprintf(stderr,
              "ERROR: %s is a specification variable\n",
              node.lhs->name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    std::string name = node.lhs->name;
    if (light_mats.count(name)) {
      // Convert to relational variable access

      // Build up name
      std::string base = name;
      assert(!node.rhs.empty());
      assert(node.rhs.size() <= 2);
      for (size_t i = 0; i < node.rhs.size(); ++i) {
        Expression* exp = node.rhs.at(i);
        RelationalInt* index = dynamic_cast<RelationalInt*>(exp);
        assert(index);
        base += "-" + std::to_string(index->value);
      }

      // Construct relational var and proceed with it
      Var v(base);
      RelationalVar rv(node.relation, &v);
      return rv.accept(*this);
    }

    switch (node.relation) {
      case ORIGINAL:
        name += "<o>";
        break;
      case RELAXED:
        name += "<r>";
        break;
    }

    unsigned version = var_version.at(name);
    name += "-" + std::to_string(version);
    z3::func_decl* array = vectors.at(name);
    z3pair i1 = node.rhs.at(0)->accept(*this);
    assert(array);
    assert(i1.original);
    assert(!i1.relaxed);

    z3::expr* expr = nullptr;
    switch (node.rhs.size()) {
      case 1:
        expr = new z3::expr((*array)(*i1.original));
        break;
      case 2:
        {
          z3pair i2 = node.rhs.at(1)->accept(*this);
          assert(i2.original);
          assert(!i2.relaxed);
          expr = new z3::expr((*array)(*i1.original, *i2.original));
        }
        break;
      default:
        // TODO: Up to 5
        assert(false);
        break;
    }
    assert(expr);

    expr_type = types.at(node.lhs->name);

    return {expr, nullptr};
  }

  z3pair CHLVisitor::visit(SpecArrayAccess &node) {
    // TODO: Allow for spec array accesses for light mats
    assert(!light_mats.count(node.lhs->name));

    if (!specvars.count(node.lhs->name)) {
      fprintf(stderr,
              "ERROR: %s is not a specification variable\n",
              node.lhs->name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    // Construct RelationalArrayAccess 
    RelationalArrayAccess arac(RELAXED, node.lhs, node.rhs, false);

    return arac.accept(*this);
  }

  void
  CHLVisitor::if_same(z3::expr original, z3::expr relaxed, Statement* body) {
    assert(body);
    z3::expr* prefix = nullptr;

    solver->push();
    add_constraint(original);
    add_constraint(relaxed);
    z3::check_result res = check(false);
    solver->pop();
    switch (res) {
      case z3::sat:
      case z3::unknown:
        // Check if_body in lockstep
        prefix = new z3::expr(original && relaxed);
        push_prefix(prefix);
        body->accept(*this);
        pop_prefix();
        break;
      case z3::unsat:
        // Do nothing
        break;
    }
  }

  void CHLVisitor::if_diff(z3::expr original,
                           z3::expr relaxed,
                           Statement* obody,
                           Statement* rbody) {
    assert(obody);
    assert(rbody);
    z3::expr* prefix = nullptr;

    solver->push();
    add_constraint(original);
    add_constraint(relaxed);
    z3::check_result res = check(false);
    solver->pop();
    switch (res) {
      case z3::sat:
        prefix = new z3::expr(original && relaxed);
        push_prefix(prefix);

        // Check body<o>
        ++ignore_relaxed;
        obody->accept(*this);
        --ignore_relaxed;

        // Check body<r>
        ++ignore_original;
        rbody->accept(*this);
        --ignore_original;

        pop_prefix();
        break;
      case z3::unsat:
        // Do nothing
        break;
      case z3::unknown:
        if (in_houdini) {
          // Give up on this run
          inner_h_unknown = true;
          break;
        } else {
          // This hopefully never happens
          assert(false);
        }
    }
  }

  z3pair CHLVisitor::visit(If &node) {
    // TODO: Test nesting
    z3pair cond = node.cond->accept(*this);
    assert(cond.original);
    assert(cond.relaxed);

    // Case 1: cond<o> && cond<r>
    star_line();
    debug_print("if cond<o> && cond<r>:");
    if_same(*cond.original, *cond.relaxed, node.if_body);

    // Case 2: cond<o> && !cond<r>
    star_line();
    debug_print("if cond<o> && !cond<r>:");
    if_diff(*cond.original, !*cond.relaxed, node.if_body, node.else_body);

    // Case 3: !cond<o> && cond<r>
    star_line();
    debug_print("if !cond<o> && cond<r>:");
    if_diff(!*cond.original, *cond.relaxed, node.else_body, node.if_body);

    // Case 4: !cond<o> && !cond<r>
    star_line();
    debug_print("if !cond<o> && !cond<r>:");
    if_same(!*cond.original, !*cond.relaxed, node.else_body);
    star_line();

    return {nullptr, nullptr};
  }

  bool CHLVisitor::check_loop(While &node, z3::expr cond) {
    if (inner_h_unknown) {
      return true;
    }
    inner_h_unknown = false;

    // New solver state for loop
    z3::solver* old_solver = solver;
    solver = new z3::solver(*context);

    // Get modern inv and add it to the solver state
    z3::expr* eqs = houdini_to_constraints(node);
    assert(eqs);
    add_constraint(*eqs);

    if (!in_houdini) {
      z3pair inv = node.inv->accept(*this);
      assert(inv.original);
      assert(!inv.relaxed);
      add_constraint(*inv.original);
    }

    // Add cond to state
    add_constraint(cond);

    // Check body
    debug_print("Body:");
    node.body->accept(*this);

    // Check houdini constraints
    debug_print("Houdini invariant: " + std::to_string(while_count));
    eqs = houdini_to_constraints(node);
    solver->push();
    add_checked_constraint(*eqs);
    z3::check_result h_res = check(!in_houdini);
    solver->pop();

    if (in_houdini) {
      parse_z3_model();
    } else {
      // Get post-body invariant
      z3pair inv = node.inv->accept(*this);

      // Check post-body invariant
      debug_print("Post body invariant: " + std::to_string(while_count));
      solver->push();
      add_checked_constraint(*inv.original);
      check();
      solver->pop();
    }

    // Restore old solver
    delete solver;
    solver = old_solver;

    bool ret = h_res == z3::unknown || inner_h_unknown;

    inner_h_unknown = false;

    return ret;
  }

  void CHLVisitor::legal_path(z3::expr& original,
                              z3::expr& relaxed,
                              z3::expr& inv,
                              const While& node,
                              std::array<z3::check_result, 3>& results) {
    // New solver for evaluating legal paths
    z3::solver* old_solver = solver;
    z3::solver path_solver(*context);
    solver = &path_solver;

    // Ignore  ignores
    unsigned old_ignore_original = ignore_original;
    unsigned old_ignore_relaxed = ignore_relaxed;

    // Add inv to virgin solver
    path_solver.add(inv);

    // Add houdini vars
    z3::expr* houdini = houdini_to_constraints(node);
    path_solver.add(*houdini);

    // Case 1: cond<o> && cond<r>
    path_solver.push();
    path_solver.add(original);
    path_solver.add(relaxed);
    debug_print(std::to_string(while_count) + " : check path cond<o> && cond<r>");
    results.at(0) = check(false);
    path_solver.pop();

    // Case 2: cond<o> && !cond<r>
    path_solver.push();
    path_solver.add(original);
    path_solver.add(!relaxed);
    debug_print(std::to_string(while_count) + " : check path cond<o> && !cond<r>");
    results.at(1) = check(false);
    path_solver.pop();

    // Case 3: !cond<o> && cond<r>
    path_solver.push();
    path_solver.add(!original);
    path_solver.add(relaxed);
    debug_print(std::to_string(while_count) + " : check path !cond<o> && cond<r>");
    results.at(2) = check(false);
    path_solver.pop();

    // Case 4: !cond<o> && !cond<r>
    // Loop doesn't run, do nothing.

    // Restore old solver and ignore state
    solver = old_solver;
    ignore_original = old_ignore_original;
    ignore_relaxed = old_ignore_relaxed;
  }

  z3::expr* CHLVisitor::houdini_to_constraints(const While& node) {
    const std::vector<std::string>& houdini_vars = in_houdini ? *cur_houdini_vars :
                                                                node.houdini_vars;
    assert(in_houdini == bool(cur_houdini_vars));
    z3::expr ret(context->bool_val(true));

    if (houdini_failed) return new z3::expr(ret);

    h_tmps.clear();
    for (const std::string& var : houdini_vars) {
      // Leverage existing binop logic
      Var v(var);
      RelationalVar ovar(ORIGINAL, &v);
      RelationalVar rvar(RELAXED, &v);
      RelationalBoolExp eq(EQUALS, &ovar, &rvar);

      z3pair res = eq.accept(*this);
      assert(res.original);
      assert(!res.relaxed);

      std::string tmp_name = H_TMP_PREFIX + std::to_string(h_tmp++);
      h_tmps.push_back(tmp_name);

      z3::expr tmp = context->bool_const(tmp_name.c_str());

      add_constraint(tmp == *res.original);

      ret = ret && tmp;
    }

    return new z3::expr(ret);
  }

  z3pair CHLVisitor::visit(While &node) {
    assert((!cur_houdini_vars && !in_houdini) || in_houdini);

    ++while_count;

    z3pair inv = {nullptr, nullptr};
    if (!in_houdini) {
      // Verify invariant at top of loop
      inv = node.inv->accept(*this);
      assert(inv.original);
      assert(!inv.relaxed);
      debug_print("Pre body invariant: " + std::to_string(while_count));
      solver->push();
      add_checked_constraint(*inv.original);
      check();
      solver->pop();

      if (node.inf) {
        assert(!in_houdini);
        assert(node.houdini_vars.empty());
        assert(!cur_houdini_vars);
        in_houdini = true;
        passed_houdini_pre = false;
        outer_h_unknown = false;

        cur_houdini_vars = &node.houdini_vars;
        for (const std::pair<std::string, type_t>& kv : types) {
          if (!specvars.count(kv.first)) {
            node.houdini_vars.push_back(kv.first);
          }
        }

        do {
          if (outer_h_unknown) {

            debug_print("Houdini came up unknown, trying weak Houdini");
            std::vector<std::string> old_h_vars(node.houdini_vars);
            std::vector<std::string> old_h_tmps(h_tmps);
            assert(old_h_vars.size() == old_h_tmps.size());
            std::vector<std::string> new_h_vars;
            std::vector<std::string> new_h_tmps;
            for (size_t i = 0; i < old_h_vars.size(); ++i) {
              node.houdini_vars.clear();
              h_tmps.clear();
              std::string var = old_h_vars.at(i);
              std::string tmp = old_h_tmps.at(i);
              node.houdini_vars.push_back(var);
              h_tmps.push_back(tmp);
              houdini_failed = false;
              outer_h_unknown = false;
              passed_houdini_pre = false;

              debug_print("Trying weak Houdini var: " + houdini_to_str());

              node.accept(*this);

              if (!node.houdini_vars.empty() && !outer_h_unknown) {
                assert(node.houdini_vars.size() == 1);
                assert(h_tmps.size() == 1);

                new_h_vars.push_back(var);
                new_h_tmps.push_back(tmp);

                debug_print("Saving weak Houdini var: " + var);
              } else {
                debug_print("Rejecting weak Houdini var: " + var);
              }
            }

            node.houdini_vars = new_h_vars;
            h_tmps = new_h_tmps;
            houdini_failed = false;
            passed_houdini_pre = true;
          } else {
            debug_print("Trying Houdini vars: " + houdini_to_str());
            houdini_failed = false;
            node.accept(*this);
          }
        } while (houdini_failed);
        debug_print("Found Houdini vars: " + houdini_to_str());

        in_houdini = false;
        cur_houdini_vars = nullptr;
      }
    }
    star_line();
    debug_print("While: " + std::to_string(while_count));

    // Verify houdini invariant
    bool h_unknown = false;
    z3::expr* eqs = houdini_to_constraints(node);
    if (!passed_houdini_pre || &node.houdini_vars != cur_houdini_vars) {
      debug_print("Pre body houdini: " + std::to_string(while_count));
      solver->push();
      add_checked_constraint(*eqs);
      z3::check_result h_res =  check(!in_houdini);
      h_unknown = h_res == z3::unknown || h_unknown;
      solver->pop();
      if (in_houdini) {
        parse_z3_model();
        if (houdini_failed) {
          --while_count;
          return {nullptr, nullptr};
        }

        if (&node.houdini_vars == cur_houdini_vars) passed_houdini_pre = true;
      }
    }



    assert((in_houdini && !inv.original) ||
           (!in_houdini && inv.original));
    assert(!inv.relaxed);

    // Evaluate condition
    z3pair cond = node.cond->accept(*this);
    assert(cond.original);
    assert(cond.relaxed);

    z3::expr path_inv = in_houdini ? *eqs : (*inv.original && *eqs);
    std::array<z3::check_result, 3> paths;
    legal_path(*cond.original, *cond.relaxed, path_inv, node, paths);

    // Case 1: cond<o> && cond<r>
    switch (paths.at(0)) {
      case z3::sat:
        // Check both in lockstep
        debug_print(std::to_string(while_count) + " : body cond<o> && cond<r>");
        h_unknown = check_loop(node, *cond.original && *cond.relaxed) || h_unknown;
        break;
      case z3::unsat:
        // All constraints implicitly true
        break;
      case z3::unknown:
        assert(false);
    }

    // Case 2: cond<o> && !cond<r>
    switch (paths.at(1)) {
      case z3::sat:
        {
          // Recheck cond
          solver->push();
          z3pair cond_new = node.cond->accept(*this);
          ++ignore_relaxed;
          debug_print(std::to_string(while_count) + " : body cond<o> && !cond<r>");
          h_unknown = check_loop(node, *cond_new.original && !(*cond_new.relaxed)) || h_unknown;
          --ignore_relaxed;
          solver->pop();
        }
        break;
      case z3::unsat:
        // Do nothing
        break;
      case z3::unknown:
        assert(false);
    }

    // Case 3: !cond<o> && cond<r>
    switch (paths.at(2)) {
      case z3::sat:
        {
          // Recheck cond
          solver->push();
          z3pair cond_new = node.cond->accept(*this);
          ++ignore_original;
          debug_print(std::to_string(while_count) + " : body !cond<o> && cond<r>");
          h_unknown = check_loop(node, !(*cond_new.original) && *cond_new.relaxed) || h_unknown;
          --ignore_original;
          solver->pop();
        }
        break;
      case z3::unsat:
        // Do nothing
        break;
      case z3::unknown:
        assert(false);
    }

    if (h_unknown && in_houdini && &node.houdini_vars == cur_houdini_vars) {
      outer_h_unknown = h_unknown;
      houdini_failed = true;
      --while_count;
      return {nullptr, nullptr};
    }

    // Case 4: !cond<o> && !cond<r>
    // Do nothing

    // After loop we get !cond && inv (though they must be re-evaluated to get
    // the propper versions).  We also need the OLD invarient in case the loop
    // did not run
    cond = node.cond->accept(*this);
    assert(cond.original);
    assert(cond.relaxed);
    add_constraint(!*cond.original);
    add_constraint(!*cond.relaxed);
    if (!in_houdini) {
      inv = node.inv->accept(*this);
      assert(inv.original);
      assert(!inv.relaxed);
      add_constraint(*inv.original);
    }
    if (!h_unknown) {
      eqs = houdini_to_constraints(node);
      add_constraint(*eqs);
    }
    --while_count;

    node.seen = true;
    if (!in_houdini) node.houdini_vars.clear();
    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(ModelDeref &node) {
    z3::expr* ret = model_visitor->get_current_var(node.var->name);
    expr_type = model_visitor->get_var_type(node.var->name);
    return {ret, ret};
  }

  z3pair CHLVisitor::visit(RelationalModelDeref &node) {
    z3::expr* ret = model_visitor->get_current_var(node.var->name);
    expr_type = model_visitor->get_var_type(node.var->name);
    return {ret, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalNormal &node) {
    z3pair var = node.exp->accept(*this);
    assert(var.original);
    assert(!var.relaxed);
    Z3_ast norm = Z3_mk_fpa_is_normal(*context, *var.original);
    z3::expr* ret = new z3::expr(z3::to_expr(*context, norm));
    return {ret, nullptr};
  }

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
  z3pair CHLVisitor::visit(Skip &node) {
    // Do nothing
    return {nullptr, nullptr};
  }
#pragma clang diagnostic pop

  z3pair CHLVisitor::visit(Copy &node) {
    vec_pair src = {get_current_vec(node.src->name + "<o>"),
                    get_current_vec(node.src->name + "<r>")};
    std::string odest = node.dest->name + "<o>";
    std::string rdest = node.dest->name + "<r>";

    // Construct new destination array
    assert(var_version.at(odest) == var_version.at(rdest));
    unsigned version = var_version.at(odest) + 1;
    ++var_version.at(odest);
    ++var_version.at(rdest);
    odest += "-" + std::to_string(version);
    rdest += "-" + std::to_string(version);
    vec_pair dest = add_vector(types.at(node.dest->name),
                             odest,
                             rdest,
                             *dim_map.at(node.dest->name));

    // Set all values equal
    // TODO: Support 2d arrays here
    std::vector<z3::expr*>* dimensions = dim_map.at(node.dest->name);
    assert(dimensions->size() == 1);
    add_constraint(*(vector_equals(*dest.original,
                                   *src.original,
                                   *dimensions,
                                   IGNORE_1D)));
    add_constraint(*(vector_equals(*dest.relaxed,
                                   *src.relaxed,
                                   *dimensions,
                                   IGNORE_1D)));

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(Exponent &node) {
    assert(node.base);
    assert(node.exp);
    z3pair base = node.base->accept(*this);
    z3pair exp = node.exp->accept(*this);
    assert(base.original);
    assert(base.relaxed);
    assert(exp.original);
    assert(exp.relaxed);

    z3::expr* res_o = new z3::expr(z3::pw(*base.original, *exp.original));
    z3::expr* res_r = new z3::expr(z3::pw(*base.relaxed, *exp.relaxed));
    assert(res_o);
    assert(res_r);

    return {res_o, res_r};
  }

  z3pair CHLVisitor::visit(RelationalForall &node) {
    assert(node.var);
    assert(node.exp);

    // Generate var names
    std::string oname = node.var->name + "<o>";
    std::string rname = node.var->name + "<r>";
    std::string tmp_base = "forall-tmp-" + std::to_string(forall_ctr);
    std::string otmp = tmp_base + "<o>";
    std::string rtmp = tmp_base + "<r>";
    ++forall_ctr;

    // Verify that this var does not exist
    assert(!contains_var(oname));
    assert(!contains_var(rname));

    // Add var
    // TODO: Support more than just ints
    // TODO: Do something more intelligent than forcing that <o> is used
    //       Or at least detect if <r> is used and fail
    add_var(type_t::INT, otmp, rtmp);
    types[node.var->name] = type_t::INT;
    specvars.insert(node.var->name);
    z3::expr* var = get_current_var(rtmp);
    assert(var);

    // Map var name to tmp var
    var_version[rname] = 0;
    vars[rname + "-0"] = var;

    // Eval expression
    z3pair exp = node.exp->accept(*this);
    assert(exp.original);
    assert(!exp.relaxed);

    // Construct forall
    z3::expr *ret = new z3::expr(z3::forall(*var, *exp.original));
    assert(ret);

    // Remove the forall var
    size_t res = var_version.erase(rname);
    assert(res);
    res = vars.erase(rname + "-0");
    assert(res);
    res = types.erase(node.var->name);
    assert(res);
    res = specvars.erase(node.var->name);
    assert(res);

    return {ret, nullptr};
  }

  void CHLVisitor::parse_z3_model() {
    if (houdini_failed || !z3_model) return;

    houdini_failed = true;


    // Build up mapping of const assignments
    std::unordered_map<std::string, std::string> assignments;
    for (unsigned i = 0; i < z3_model->num_consts(); ++i) {
      z3::func_decl decl = z3_model->get_const_decl(i);
      z3::expr interp = z3_model->get_const_interp(decl);

      std::stringstream name_ss;
      std::stringstream val_ss;

      name_ss << decl.name();
      val_ss << interp;

      auto res = assignments.emplace(name_ss.str(), val_ss.str());
      assert(res.second);
    }

    // Check which var eqs mapped to "false" and remove them
    std::cout << cur_houdini_vars->size() << " " << h_tmps.size() << std::endl;
    assert(cur_houdini_vars);
    assert(cur_houdini_vars->size() == h_tmps.size());
    for (unsigned i = 0; i < h_tmps.size();) {
      std::string val = assignments.at(h_tmps.at(i));
      assert(val == "true" || val == "false");

      if (val == "false") {
        h_tmps.erase(h_tmps.begin() + i);
        cur_houdini_vars->erase(cur_houdini_vars->begin() + i);
      } else {
        ++i;
      }
    }

    assert(cur_houdini_vars->size() == h_tmps.size());
  }

  std::string CHLVisitor::houdini_to_str() {
    std::string ret = "";

    for (const std::string& var : *cur_houdini_vars) {
      ret += var + ", ";
    }

    return ret;
  }
}


