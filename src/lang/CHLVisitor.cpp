#include <cstdio>
#include <cstring>

#include "CHLVisitor.h"
#include "ConjunctionBreaker.h"
#include "PrintVisitor.h"

#define BUF_SIZE 16
#define Z3_TMP "/tmp/constraints.smt2"

static const int EXIT_RUNTIME_ERROR = 2;
// timeout in milliseconds
static const int TIMEOUT = 10000;
// Unstoppable timeout in seconds
static const int SUPER_TIMEOUT = (TIMEOUT / 1000) * 2;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wexit-time-destructors"
#pragma clang diagnostic ignored "-Wglobal-constructors"
static std::vector<z3::expr*> IGNORE_1D = {nullptr};
static std::vector<z3::expr*> IGNORE_2D = {nullptr, nullptr};
static const std::string H_TMP_PREFIX = "h-tmp-";
static const std::string Z3_BIN = "timeout -s 9 " +
                                  std::to_string(SUPER_TIMEOUT) +
                                  "s z3 -t:" +
                                  std::to_string(TIMEOUT) +
                                  " -smt2 " + Z3_TMP;
#pragma clang diagnostic pop



namespace lang {

  CHLVisitor::CHLVisitor(z3::context* context_,
                         z3::solver* solver_,
                         model::Z3Visitor* model_visitor_,
                         std::ofstream& z3_log_,
                         std::ofstream& smt2_log_) : context(context_),
                                                     z3_log(z3_log_),
                                                     smt2_log(smt2_log_) {
    //z3::set_param(":timeout", TIMEOUT);
    z3::set_param("smt.timeout", TIMEOUT);
    solver = solver_;
    model_visitor = model_visitor_;
    in_assign = false;
    errors = 0;
    ignore_original = ignore_relaxed = 0;
    unsat_context = false;
    unknown_context = false;
    in_houdini = false;
    in_weak_houdini = false;
    forall_i = new z3::expr(this->context->int_const("forall_i"));
    forall_j = new z3::expr(this->context->int_const("forall_j"));
    quantifier_ctr = 0;
    constraints_generated = 0;
    num_inferred = 0;
    total_paths = 0;
    pruned_paths = 0;
    z3_model = nullptr;
    houdini_failed = false;
    h_tmp = 0;
    passed_houdini_pre = false;
    cur_houdini_invs = nullptr;
    cur_nonrel_houdini_invs = nullptr;
    inner_h_unknown = false;
    parent_while = nullptr;
    parent_function = nullptr;
    h_var_version = nullptr;
    assume_eq = true;
  }

  static void debug_print(const std::string &str) {
#ifndef NDEBUG
    std::cout << str << std::endl;
#endif
  }


  static z3::check_result z3_bin(const std::string& constraints,
                                 bool add_check_sat) {
    int res;

    // Write constraints to temp file
    std::ofstream tmp(Z3_TMP, std::ios_base::trunc);
    tmp << constraints << std::endl;
    if (add_check_sat) tmp << "(check-sat)" << std::endl;

    // Start Z3 process
    FILE* stdio = popen(Z3_BIN.c_str(), "r");
    assert(stdio);

    // Read result
    char buf[BUF_SIZE] = {0};
    size_t read = fread(buf, 1, BUF_SIZE, stdio);
    assert(feof(stdio));

    // End Z3 process
    res = pclose(stdio);
    assert(res != -1);

    // Close temp file
    tmp.close();

    if (strncmp(buf, "sat\n", BUF_SIZE) == 0) return z3::sat;
    else if (strncmp(buf, "unsat\n", BUF_SIZE) == 0) return z3::unsat;
    else if (strncmp(buf, "unknown\n", BUF_SIZE) == 0) return z3::unknown;
    else if (!read) {
      debug_print("killed");
      return z3::unknown;
    }

    assert(false);
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

  std::string CHLVisitor::get_current_var_name(std::string name) {
    unsigned version;
    try {
      version = var_version.at(name);
    } catch (const std::out_of_range&) {
      return "";
    }
    return name + "-" + std::to_string(version);
  }

  z3::expr* CHLVisitor::get_current_var(std::string name) {
    std::string vname = get_current_var_name(name);
    if (name.empty()) {
      std::cerr << "No such var: " << name << std::endl;
      exit(1);
    }
    return vars.at(vname);
  }

  z3::func_decl* CHLVisitor::get_current_vec(std::string name) {
    std::string vname = get_current_var_name(name);
    if (name.empty()) {
      std::cerr << "No such matrix: " << name << std::endl;
      exit(1);
    }
    return vectors.at(vname);
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

  void CHLVisitor::handle_uint_read(std::string name, bool is_vec) {
    std::string vname = get_current_var_name(name);
    if (vname.empty()) {
      std::cerr << "No such var: " << name << std::endl;
      exit(1);
    }
    if (cached_uints.count(vname)) return;
    cached_uints.insert(vname);

    if (is_vec) {
      const dim_vec* dim = dim_map.at(name);
      z3::func_decl* vec = get_current_vec(name);
      switch (dim->size()) {
        case 1:
          solver->add(z3::forall(*forall_i, 0 <= (*vec)(*forall_i)));
          break;
        case 2:
          solver->add(z3::forall(*forall_i,
                                 *forall_j,
                                 0 <= (*vec)(*forall_i, *forall_j)));
          break;
        default:
          assert(false);
      }
    } else {
      z3::expr* var = get_current_var(name);
      solver->add(0 <= *var);
    }

    ++constraints_generated;
  }

  z3::expr CHLVisitor::get_constraint(const z3::expr& constraint,
                                      bool invert) {
    if (prefixes.empty()) {
      return constraint;
    } else {
      z3::expr impl = *prefixes.at(0);
      for (size_t i = 1; i < prefixes.size(); ++i) {
        impl = impl && *prefixes.at(i);
      }
      if (invert) impl = !impl;
      return z3::implies(impl, constraint);
    }
  }

  void CHLVisitor::add_constraint(const z3::expr& constraint,
                                  bool invert) {
    ++constraints_generated;
    solver->add(get_constraint(constraint, invert));
  }

  void CHLVisitor::add_checked_constraint(const z3::expr& constraint) {
    ++constraints_generated;
    check_context();
    solver->add(!get_constraint(constraint, false));
  }

  void CHLVisitor::assume_prefixes() {
    for (const z3::expr* prefix : prefixes) {
      ++constraints_generated;
      solver->add(*prefix);
    }
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
      case UINT:
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
                                      const dim_vec& dimensions,
                                      std::vector<z3::expr*>& ignore_index) {
    assert(ignore_index.size() == dimensions.size());

    z3::expr *ret = nullptr;
    switch (dimensions.size()) {
      case 1:
        {
          z3::expr bounds = (*forall_i >= context->int_val(0)) &&
                            (*forall_i < *dimensions.at(0).original);
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
                            (*forall_i < *dimensions.at(0).original) &&
                            (*forall_j >= context->int_val(0)) &&
                            (*forall_j < *dimensions.at(1).original);
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
                                  const dim_vec& dimensions) {
    z3::func_decl* ofun = nullptr;
    z3::func_decl* rfun = nullptr;
    z3::sort is = context->int_sort();
    z3::sort rs = context->real_sort();
    z3::sort fs = z3::sort(*context, Z3_mk_fpa_sort_single(*context));
    switch (dimensions.size()) {
      case 1:
        switch (type) {
          case INT:
          case UINT:
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
          case UINT:
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
      if (assume_eq) add_constraint(*res.original == *res.relaxed);

      if (node.region) regions[var->name] = node.region->name;
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(DeclareMat &node) {
    for (VarList* head = node.vars; head; head = head->cdr) {
      Var* var = head->car;

      // Build dimension vector
      if (head->dimensions.empty()) {
        std::cerr << "ERROR:  Matrix "
                  << var->name
                  << " has no dimensions."
                  << std::endl;
        exit(1);
      }
      dim_vec* dimensions = new dim_vec();
      for (Expression* expr : head->dimensions) {
        assert(expr);
        z3pair res = expr->accept(*this);
        assert(res.original);
        assert(res.relaxed);
        dimensions->push_back({res.original, res.relaxed});

        // Assume dimensions are equal
        add_constraint(*res.original == *res.relaxed);
      }

      // Declare var<o> and var<r>
      std::string oname = var->name + "<o>";
      std::string rname = var->name + "<r>";
      var_version[oname] = 0;
      var_version[rname] = 0;
      dim_map[var->name] = dim_map[oname] = dim_map[rname] = dimensions;
      oname += "-0";
      rname += "-0";
      vec_pair res = add_vector(node.type, oname, rname, *dimensions);

      types[var->name] = node.type;

      if (node.specvar) specvars.insert(var->name);

      // Assume vectors are equal at declare time
      if  (assume_eq) {
        z3::expr* eq = vector_equals(*res.original,
                                     *res.relaxed,
                                     *dimensions,
                                     dimensions->size() == 1 ? IGNORE_1D : IGNORE_2D);
        add_constraint(*eq);
      }

      if (node.region) regions[var->name] = node.region->name;
    }

    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(DeclareLMat &node) {
    assert(node.type != UINT);

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

    // TODO: Support uints
    assert(expr_type != UINT);

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
    last_base_name = nullptr;
    z3pair lhs = node.lhs->accept(*this);
    type_t lhs_type = expr_type;
    assert(last_base_name);
    /*
    if (regions.count(*last_base_name)) {
      FaultyWrite fwrite(node.lhs, node.rhs);
      return fwrite.accept(*this);
    }
    */

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
    lhs = node.lhs->accept(*this);
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
      if (lhs_type == UINT) {
        ores = new z3::expr(z3::implies(0 <= *rhs.original,
                                        *lhs.original == *rhs.original));
      } else ores = new z3::expr(*lhs.original == *rhs.original);
    } else {
      // Set LHS<o> == LHS<o>-prev
      ores = new z3::expr(*lhs.original == *old_o);
    }
    assert(ores);
    add_constraint(*ores);
    if (!prefixes.empty()) add_constraint(*lhs.original == *old_o, true);

    // Set LHS<r> == RHS<r>
    z3::expr *rres = nullptr;
    model_visitor->var_equality = nullptr;
    if (!ignore_relaxed) {
      if (model_visitor->prepped()) {
        if (lhs_type == UINT) {
          std::string tname = H_TMP_PREFIX + std::to_string(h_tmp++);
          z3::expr tmp = context->int_const(tname.c_str());
          z3::expr* replacement = model_visitor->replace_op(lhs_type, &tmp);
          add_constraint(*replacement);
          rres = new z3::expr(z3::implies(0 <= tmp, *lhs.relaxed == tmp));
        } else rres = model_visitor->replace_op(lhs_type, lhs.relaxed);
        if (!prefixes.empty()) {
          for (const std::string& var : *model_visitor->updated) {
            z3::expr* cur = model_visitor->get_current_var(var);
            z3::expr* prev = model_visitor->get_previous_var(var);
            add_constraint(*cur == *prev, true);
          }
        }
      } else if (lhs_type == UINT) {
        rres = new z3::expr(z3::implies(0 <= *rhs.relaxed,
                                        *lhs.relaxed == *rhs.relaxed));
      } else rres = new z3::expr(*lhs.relaxed == *rhs.relaxed);
    } else {
      rres = new z3::expr(*lhs.relaxed == *old_r);
    }
    assert(rres);
    add_constraint(*rres);
    if (!prefixes.empty()) {
      add_constraint(*lhs.relaxed == *old_r, true);
      z3::expr* var_eq = model_visitor->var_equality;
      if (var_eq) add_constraint(*var_eq, true);
    }

    return {ores, rres};
  }

  z3pair CHLVisitor::visit(Var &node) {
    // Perform substitution if necessary
    std::string name = substitutions.count(node.name) ?
                       substitutions.at(node.name) :
                       node.name;

    // Unversioned var names
    last_base_name = new std::string(name);
    std::string oname = name + "<o>";
    std::string rname = name + "<r>";
    z3::expr* oexpr = nullptr;
    z3::expr* rexpr = nullptr;
    try {
      expr_type = types.at(name);
    } catch (const std::out_of_range&) {
      std::cerr << "No such var: " << name << std::endl;
      exit(1);
    }
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
        case UINT:
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
      bool is_light_mat = light_mats.count(name);
      if (is_light_mat || !contains_var(oname)) {
        // Working with undereferenced array, do backchannel return
        if (is_light_mat) {
          assert(expr_type != UINT);
          last_light_dim = light_dim_map.at(name);
        } else {
          z3::func_decl* ovec = get_current_vec(oname);
          z3::func_decl* rvec = get_current_vec(rname);
          last_array = {ovec, rvec};
          last_dim = dim_map.at(name);

          if (expr_type == UINT) {
            handle_uint_read(oname, true);
            handle_uint_read(rname, true);
          }
        }
        return {nullptr, nullptr};
      }

      unsigned version = var_version.at(oname);
      assert(version == var_version.at(rname));

      oexpr = vars.at(oname + "-" + std::to_string(version));
      rexpr = vars.at(rname + "-" + std::to_string(version));

      if (expr_type == UINT) {
        handle_uint_read(oname, false);
        handle_uint_read(rname, false);
      }
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
    assert (lhs_type == REAL || lhs_type == INT || lhs_type == UINT);
    assert (expr_type == REAL || expr_type == INT || expr_type == UINT);
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
    type_t dest_type = expr_type;
    in_assign = false;
    z3pair val = node.val->accept(*this);

    assert(dest.original);
    assert(dest.relaxed);
    assert(val.original);
    assert(val.relaxed);
    assert(old_o);
    assert(old_r);

    if (!ignore_relaxed) {
      model_visitor->var_equality = nullptr;
      if (dest_type == UINT) {
        std::string tname = H_TMP_PREFIX + std::to_string(h_tmp++);
        z3::expr tmp = context->int_const(tname.c_str());
        model_visitor->prep_op(FWRITE, &tmp, val.relaxed);
        z3::expr* replacement = model_visitor->replace_op(dest_type, nullptr);
        add_constraint(*replacement);
        add_constraint(z3::implies(0 <= tmp, (tmp == *dest.relaxed)));
      } else {
        model_visitor->prep_op(FWRITE, dest.relaxed, val.relaxed);
        z3::expr* res = model_visitor->replace_op(dest_type, nullptr);
        add_constraint(*res);
      }
      if (!prefixes.empty()) {
        add_constraint(*model_visitor->var_equality, true);
      }
    } else {
      add_constraint(*dest.relaxed == *old_r);
    }

    if (!ignore_original) {
      if (dest_type == UINT) {
        add_constraint(z3::implies(0 <= *val.original,
                                   *dest.original == *val.original));
      } else {
        z3::expr res = (*dest.original == *val.original);
        add_constraint(res);
      }
    } else {
      add_constraint(*dest.original == *old_o);
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
          case UINT:
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
          case UINT:
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
    std::string name = substitutions.count(node.var->name) ?
                       substitutions.at(node.var->name) :
                       node.var->name;

    if (node.check_spec && specvars.count(name)) {
      fprintf(stderr,
              "ERROR: %s is a specification variable\n",
              name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }
    last_base_name = new std::string(name);
    expr_type = types.at(name);
    std::string qname;
    switch (node.relation) {
      case ORIGINAL:
        qname = name + "<o>";
        break;
      case RELAXED:
        qname = name + "<r>";
        break;
    }

    bool is_light_mat = light_mats.count(name);
    if (!is_light_mat && contains_var(qname)) {
      z3::expr* ret = get_current_var(qname);

      if (expr_type == UINT) handle_uint_read(qname, false);

      return {ret, nullptr};
    }

    // Working with an undereferenced array, need to do backchannel return
    if (is_light_mat) last_light_dim = light_dim_map.at(name);
    else {
      z3::func_decl* arr = get_current_vec(qname);
      last_array = {arr, nullptr};
      assert(last_array.original);
      last_dim = dim_map.at(name);

      if (expr_type == UINT) handle_uint_read(qname, true);
    }
    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(SpecVar &node) {
    std::string name = substitutions.count(node.var->name) ?
                       substitutions.at(node.var->name) :
                       node.var->name;

    if (!specvars.count(name)) {
      fprintf(stderr,
              "ERROR: %s is not a specification variable\n",
              name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    // TODO: Allow light specmats
    assert (!light_mats.count(name));

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
            case UINT:
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
            case UINT:
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
          res = new z3::expr((*lhs.original || *rhs.original) &&
                             !(*lhs.original && *rhs.original));
          break;
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

    add_constraint(*assumption.original);
    return {nullptr, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalAssert &node) {
    if (ignore_relaxed) RETURN_VOID;

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
#ifndef NDEBUG
    std::cout << *solver << std::endl;
    z3_log << *solver << std::endl << std::endl;
    smt2_log << solver->to_smt2() << std::endl << std::endl;
#endif

    z3::check_result res = in_weak_houdini ? z3::unknown : solver->check();
#ifndef NDEBUG
    std::cout << res << std::endl;
#endif

    // Clear Z3 model
    delete z3_model;
    z3_model = nullptr;

    switch (res) {
      case z3::unsat:
        break;
      case z3::sat:
        z3_model = new z3::model(solver->get_model());
#ifndef NDEBUG
        std::cout << *z3_model << std::endl;
#endif
        if(exit_on_sat) {
          ++errors;
          // TODO: Remove this
          exit(1);
        }
        break;
      case z3::unknown:
        {
#ifndef NDEBUG
          std::cout << "reason: ";
          if (in_weak_houdini) std::cout << "in weak houdini";
          else std::cout << solver->reason_unknown();
          std::cout << std::endl;
#endif

          if (in_houdini && !in_weak_houdini) return z3::unknown;

          // Try again with *solver output
#ifndef NDEBUG
          std::cout << "Trying again with *solver output...";
          std::cout.flush();
#endif
          std::ostringstream constraints;
          constraints << *solver;
          res = z3_bin(constraints.str(), true);
#ifndef NDEBUG
          std::cout << res << std::endl;
#endif
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
#ifndef NDEBUG
              std::cout << "Trying again with smt2 output...";
              std::cout.flush();
#endif
              res = z3_bin(solver->to_smt2(), false);
#ifndef NDEBUG
              std::cout << res << std::endl;
#endif
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
    assert (lhs_type == REAL || lhs_type == INT || lhs_type == UINT);
    assert (expr_type == REAL || expr_type == INT || expr_type == UINT);
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
    const std::string& node_name = node.lhs->name;
    if (labels.count(node_name)) {
      assert(node.rhs.size() == 1);
      model_visitor->frame = node_name;
      return node.rhs.at(0)->accept(*this);
    }

    const std::string& name = substitutions.count(node_name) ?
                              substitutions.at(node_name) :
                              node_name;

    last_base_name = new std::string(name);

    if (light_mats.count(name)) {
      // Convert this to a variable access

      // Build up name
      std::string base = name;
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

    std::string oname = name + "<o>";
    std::string rname = name + "<r>";
    unsigned version = var_version.at(oname);
    assert(version == var_version.at(rname));
    z3::func_decl* oarray = get_current_vec(oname);
    z3::func_decl* rarray = get_current_vec(rname);

    // Examine index, but be careful to remove assign flag
    bool old_in_assign = in_assign;
    in_assign = false;
    z3pair i1 = node.rhs.at(0)->accept(*this);
    in_assign = old_in_assign;

    if (in_assign) {
      std::vector<z3::expr*> ignore;
      old_o = old_r = nullptr;
      type_t type = types.at(name);
      dim_vec* dimension = dim_map.at(name);
      ++version;
      ++var_version.at(name + "<o>");
      ++var_version.at(name + "<r>");
      std::string new_oname = name + "<o>-" + std::to_string(version);
      std::string new_rname = name + "<r>-" + std::to_string(version);
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
    type_t array_type = types.at(name);
    switch (node.rhs.size()) {
      case 1:
        oexpr = new z3::expr((*oarray)(*i1.original));
        rexpr = new z3::expr((*rarray)(*i1.relaxed));
        if (array_type == UINT) {
          handle_uint_read(oname, true);
          handle_uint_read(rname, true);
        }
        break;
      case 2:
        {
          z3pair i2 = node.rhs.at(1)->accept(*this);
          assert(i2.original);
          assert(i2.relaxed);
          oexpr = new z3::expr((*oarray)(*i1.original, *i2.original));
          rexpr = new z3::expr((*rarray)(*i1.relaxed, *i2.relaxed));
          if (array_type == UINT) {
            handle_uint_read(oname, true);
            handle_uint_read(rname, true);
          }
        }
        break;
      default:
        // TODO: Up to 5
        assert(false);
        break;
    }
    assert(oexpr);
    assert(rexpr);

    expr_type = array_type;

    return {oexpr, rexpr};
  }

  z3pair CHLVisitor::visit(RelationalArrayAccess &node) {
    std::string name = substitutions.count(node.lhs->name) ?
                       substitutions.at(node.lhs->name) :
                       node.lhs->name;

    if (node.check_spec && specvars.count(name)) {
      fprintf(stderr,
              "ERROR: %s is a specification variable\n",
              name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    std::string qname = name;
    if (light_mats.count(qname)) {
      // Convert to relational variable access

      // Build up name
      std::string base = qname;
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
        qname += "<o>";
        break;
      case RELAXED:
        qname += "<r>";
        break;
    }

    z3::func_decl* array = get_current_vec(qname);
    z3pair i1 = node.rhs.at(0)->accept(*this);
    assert(array);
    assert(i1.original);
    assert(!i1.relaxed);

    z3::expr* expr = nullptr;
    expr_type = types.at(name);
    switch (node.rhs.size()) {
      case 1:
        expr = new z3::expr((*array)(*i1.original));
        if (expr_type == UINT) handle_uint_read(qname, true);
        break;
      case 2:
        {
          z3pair i2 = node.rhs.at(1)->accept(*this);
          assert(i2.original);
          assert(!i2.relaxed);
          expr = new z3::expr((*array)(*i1.original, *i2.original));
          if (expr_type == UINT) handle_uint_read(qname, true);
        }
        break;
      default:
        // TODO: Up to 5
        assert(false);
        break;
    }
    assert(expr);

    return {expr, nullptr};
  }

  z3pair CHLVisitor::visit(SpecArrayAccess &node) {
    const std::string& node_name = node.lhs->name;
    if (labels.count(node_name)) {
      assert(node.rhs.size() == 1);
      model_visitor->frame = node_name;
      return node.rhs.at(0)->accept(*this);
    }

    const std::string& name = substitutions.count(node_name) ?
                              substitutions.at(node_name) :
                              node_name;

    // TODO: Allow for spec array accesses for light mats
    assert(!light_mats.count(name));

    if (!specvars.count(name)) {
      fprintf(stderr,
              "ERROR: %s is not a specification variable\n",
              name.c_str());
      exit(EXIT_RUNTIME_ERROR);
    }

    // Construct RelationalArrayAccess 
    RelationalArrayAccess arac(RELAXED, node.lhs, node.rhs, false);

    return arac.accept(*this);
  }

  void CHLVisitor::legal_if_paths(z3::expr& original,
                                  z3::expr& relaxed,
                                  std::array<z3::check_result, 4>& results) {
    // Case 1: cond<o> && cond<r>
    solver->push();
    add_constraint(original);
    add_constraint(relaxed);
    assume_prefixes();
    debug_print("check if path cond<o> && cond<r>");
    results.at(0) = check(false);
    solver->pop();

    // Case 2: cond<o> && !cond<r>
    solver->push();
    add_constraint(original);
    add_constraint(!relaxed);
    assume_prefixes();
    debug_print("check if path cond<o> && !cond<r>");
    results.at(1) = check(false);
    solver->pop();

    // Case 3: !cond<o> && cond<r>
    solver->push();
    add_constraint(!original);
    add_constraint(relaxed);
    assume_prefixes();
    debug_print("check if path !cond<o> && cond<r>");
    results.at(2) = check(false);
    solver->pop();

    // Case 4: !cond<o> && !cond<r>
    solver->push();
    add_constraint(!original);
    add_constraint(!relaxed);
    assume_prefixes();
    debug_print("check if path !cond<o> && !cond<r>");
    results.at(3) = check(false);
    solver->pop();
  }

  void
  CHLVisitor::if_same(z3::expr original, z3::expr relaxed, Statement* body) {
    assert(body);
    z3::expr* prefix = new z3::expr(original && relaxed);
    push_prefix(prefix);
    body->accept(*this);
    pop_prefix();
  }

  void CHLVisitor::if_diff(z3::expr original,
                           z3::expr relaxed,
                           Statement* obody,
                           Statement* rbody) {
    assert(obody);
    assert(rbody);
    z3::expr* prefix = new z3::expr(original && relaxed);
    push_prefix(prefix);

    // Check body<r>
    ++ignore_original;
    rbody->accept(*this);
    --ignore_original;


    // Check body<o>
    ++ignore_relaxed;
    obody->accept(*this);
    --ignore_relaxed;

    pop_prefix();
  }

  z3pair CHLVisitor::visit(If &node) {
    z3pair cond = node.cond->accept(*this);
    assert(cond.original);
    assert(cond.relaxed);

    std::array<z3::check_result, 4> paths;
    legal_if_paths(*cond.original, *cond.relaxed, paths);
    total_paths += 4;
    for (z3::check_result res : paths) {
      if (res == z3::unsat) ++pruned_paths;
    }

    // Case 1: cond<o> && cond<r>
    switch (paths.at(0)) {
      case z3::sat:
      case z3::unknown:
        star_line();
        debug_print("if cond<o> && cond<r>:");
        if_same(*cond.original, *cond.relaxed, node.if_body);
        break;
      case z3::unsat:
        break;
    }

    // Case 2: cond<o> && !cond<r>
    switch (paths.at(1)) {
      case z3::sat:
      case z3::unknown:
        star_line();
        debug_print("if cond<o> && !cond<r>:");
        if_diff(*cond.original, !*cond.relaxed, node.if_body, node.else_body);
        break;
      case z3::unsat:
        break;
    }

    // Case 3: !cond<o> && cond<r>
    switch (paths.at(2)) {
      case z3::sat:
      case z3::unknown:
        star_line();
        debug_print("if !cond<o> && cond<r>:");
        if_diff(!*cond.original, *cond.relaxed, node.else_body, node.if_body);
        break;
      case z3::unsat:
        break;
    }

    // Case 4: !cond<o> && !cond<r>
    switch (paths.at(3)) {
      case z3::sat:
      case z3::unknown:
        star_line();
        debug_print("if !cond<o> && !cond<r>:");
        if_same(!*cond.original, !*cond.relaxed, node.else_body);
        star_line();
        break;
      case z3::unsat:
        break;
    }

    return {nullptr, nullptr};
  }

  bool CHLVisitor::check_loop(While &node, z3::expr cond) {
    assert(!ignore_relaxed);

    if (inner_h_unknown) {
      return true;
    }
    inner_h_unknown = false;

    const std::string& label = node.label->name;

    // New solver state for loop
    z3::solver* old_solver = solver;
    solver = new z3::solver(*context);
    cached_uints.clear();
    model_visitor->add_frame(node.label->name);

    // Get modern inv and add it to the solver state
    h_z3pair eqs = houdini_to_constraints(node);
    assert(eqs.assumes);
    assert(eqs.asserts);
    add_constraint(*eqs.assumes);
    add_constraint(*eqs.asserts);

    z3pair inv = node.inv->accept(*this);
    assert(inv.original);
    assert(!inv.relaxed);
    add_constraint(*inv.original);

    z3pair nonrel_inv = node.nonrel_inv->accept(*this);
    assert(nonrel_inv.original);
    assert(nonrel_inv.relaxed);
    if (!ignore_original) add_constraint(*nonrel_inv.original);
    add_constraint(*nonrel_inv.relaxed);

    // Add cond to state
    add_constraint(cond);

    // Check body
    debug_print("Body:");
    node.body->accept(*this);

    // Check houdini constraints
    debug_print("Houdini invariant: " + label);
    eqs = houdini_to_constraints(node);
    solver->push();
    add_constraint(*eqs.assumes);
    add_checked_constraint(*eqs.asserts);
    z3::check_result h_res = check(!in_houdini);
    solver->pop();

    if (in_houdini) {
      parse_z3_model();
    } else {
      // Get post-body invariant
      inv = node.inv->accept(*this);
      nonrel_inv = node.nonrel_inv->accept(*this);

      // Check post-body invariant
      debug_print("Post body invariant: " + label);
      solver->push();
      if (!ignore_original) add_constraint(*nonrel_inv.original);
      add_checked_constraint(*inv.original && *nonrel_inv.relaxed);
      check();
      solver->pop();
    }

    // Restore old solver
    delete solver;
    solver = old_solver;
    cached_uints.clear();

    bool ret = h_res == z3::unknown || inner_h_unknown;

    inner_h_unknown = false;

    weak_houdini_failed = weak_houdini_failed || h_res != z3::unsat;

    return ret;
  }

  void CHLVisitor::legal_path(z3::expr& original,
                              z3::expr& relaxed,
                              z3::expr& inv,
                              const While& node,
                              std::array<z3::check_result, 3>& results) {
    assert(!ignore_relaxed);
    const std::string& label = node.label->name;

    // New solver for evaluating legal paths
    z3::solver* old_solver = solver;
    z3::solver path_solver(*context);
    solver = &path_solver;
    cached_uints.clear();

    // Ignore  ignores
    unsigned old_ignore_original = ignore_original;

    // Add inv to virgin solver
    path_solver.add(inv);

    // Add houdini invs
    h_z3pair houdini = houdini_to_constraints(node);
    path_solver.add(*houdini.assumes);
    path_solver.add(*houdini.asserts);

    if (!ignore_original) {
      // Case 1: cond<o> && cond<r>
      path_solver.push();
      path_solver.add(original);
      path_solver.add(relaxed);
      debug_print(label + " : check path cond<o> && cond<r>");
      results.at(0) = check(false);
      path_solver.pop();

      // Case 2: cond<o> && !cond<r>
      path_solver.push();
      path_solver.add(original);
      path_solver.add(!relaxed);
      debug_print(label + " : check path cond<o> && !cond<r>");
      results.at(1) = check(false);
      path_solver.pop();
    } else {
      results.at(0) = z3::unsat;
      results.at(1) = z3::unsat;
    }

    // Case 3: !cond<o> && cond<r>
    path_solver.push();
    path_solver.add(!original);
    path_solver.add(relaxed);
    debug_print(label + " : check path !cond<o> && cond<r>");
    results.at(2) = check(false);
    path_solver.pop();

    // Case 4: !cond<o> && !cond<r>
    // Loop doesn't run, do nothing.

    // Restore old solver and ignore state
    solver = old_solver;
    ignore_original = old_ignore_original;
    ignore_relaxed = false;
    cached_uints.clear();
  }

  h_z3pair CHLVisitor::houdini_to_constraints(const While& node) {
    assert(!ignore_relaxed);

    const std::vector<RelationalBoolExp*>& houdini_invs = in_houdini ? *cur_houdini_invs :
                                                                       node.houdini_invs;
    const std::vector<BoolExp*>& nonrel_houdini_invs = in_houdini ? *cur_nonrel_houdini_invs :
                                                                    node.nonrel_houdini_invs;
    assert(in_houdini == bool(cur_houdini_invs));
    assert(in_houdini == bool(cur_nonrel_houdini_invs));

    z3::expr assumes(context->bool_val(true));
    z3::expr asserts(context->bool_val(true));

    if (houdini_failed) return {new z3::expr(assumes), new z3::expr(asserts)};

    h_tmps.clear();
    for (RelationalBoolExp* inv : houdini_invs) {
      z3pair res = inv->accept(*this);
      assert(res.original);
      assert(!res.relaxed);

      std::string tmp_name = H_TMP_PREFIX + std::to_string(h_tmp++);
      h_tmps.push_back(tmp_name);

      z3::expr tmp = context->bool_const(tmp_name.c_str());

      add_constraint(tmp == *res.original);

      asserts = asserts && tmp;
    }

    nonrel_h_tmps.clear();
    for (BoolExp* inv : nonrel_houdini_invs) {
      z3pair res = inv->accept(*this);
      assert(res.original);
      assert(res.relaxed);

      std::string tmp_name = H_TMP_PREFIX + std::to_string(h_tmp++);
      nonrel_h_tmps.push_back(tmp_name);

      z3::expr tmp = context->bool_const(tmp_name.c_str());

      add_constraint(tmp == *res.relaxed);

      if (!ignore_original) assumes = assumes && res.original;

      asserts = asserts && tmp;
    }

    return {new z3::expr(assumes), new z3::expr(asserts)};
  }

  template<typename T>
  void CHLVisitor::weak_houdini(const std::vector<T>& old_invs,
                                const std::vector<std::string>& old_tmps,
                                std::vector<T>& cur_invs,
                                std::vector<std::string>& tmps,
                                std::vector<T>& new_invs,
                                std::vector<std::string>& new_tmps,
                                While& node) {
    assert(!ignore_relaxed);
    PrintVisitor pv(true);
    in_weak_houdini = true;
    for (size_t i = 0; i < old_invs.size(); ++i) {
      T h_inv = old_invs.at(i);

      // Detect whether we already have this invariant
      pv.output.clear();
      h_inv->accept(pv);
      std::string rep = pv.output;
      bool seen = false;
      for (const T& inv : new_invs) {
        pv.output.clear();
        inv->accept(pv);
        if (rep == pv.output) {
          seen = true;
          break;
        }
      }

      if (seen) continue;

      std::string tmp = old_tmps.at(i);
      cur_invs.push_back(h_inv);
      tmps.push_back(tmp);
      houdini_failed = false;
      outer_h_unknown = false;
      passed_houdini_pre = false;
      weak_houdini_failed = false;

      std::string str_rep = houdini_to_str();
      debug_print("Trying weak Houdini inv: " + str_rep);


      node.accept(*this);

      if (weak_houdini_failed || outer_h_unknown) {
        cur_invs.pop_back();
        tmps.pop_back();
        debug_print("Rejecting weak Houdini inv: " + str_rep);
      } else {
        new_invs.push_back(h_inv);
        new_tmps.push_back(tmp);
        debug_print("Saving weak Houdini inv: " + str_rep);
      }
    }
    in_weak_houdini = false;
  }

  void CHLVisitor::parent_inf(BoolExp* nonrel_inv, RelationalBoolExp* rel_inv) {
    {
      ConjunctionBreaker cb(rel_inv);
      inv_vec cb_vec = cb.fissure();
      cur_houdini_invs->insert(cur_houdini_invs->end(),
                               cb_vec.begin(),
                               cb_vec.end());
      if (parent_while) {
        cur_houdini_invs->insert(cur_houdini_invs->end(),
                                 parent_while->houdini_invs.begin(),
                                 parent_while->houdini_invs.end());
      }
    }

    {
      ConjunctionBreaker cb(nonrel_inv);
      nonrel_inv_vec cb_vec = cb.nonrel_fissure();
      cur_nonrel_houdini_invs->insert(cur_nonrel_houdini_invs->end(),
                                      cb_vec.begin(),
                                      cb_vec.end());
      if (parent_while) {
        cur_nonrel_houdini_invs->insert(cur_nonrel_houdini_invs->end(),
                                        parent_while->nonrel_houdini_invs.begin(),
                                        parent_while->nonrel_houdini_invs.end());
      }
    }
  }

  z3pair CHLVisitor::visit(While &node) {
    if (ignore_relaxed) {
      // Assume oringinal non-relational invariant
      // (but no need to check the loop)
      z3pair post = node.nonrel_inv->accept(*this);
      add_constraint(*post.original);
      RETURN_VOID;
    }

    assert((!cur_houdini_invs && !in_houdini) || in_houdini);
    assert((!cur_nonrel_houdini_invs && !in_houdini) || in_houdini);

    const std::string& label = node.label->name;
    labels.insert(label);

    version_map old_versions(var_version);

    z3pair inv = {nullptr, nullptr};
    z3pair nonrel_inv = {nullptr, nullptr};
    if (!in_houdini) {
      model_visitor->add_frame(node.label->name);

      // Verify invariant at top of loop
      inv = node.inv->accept(*this);
      assert(inv.original);
      assert(!inv.relaxed);
      nonrel_inv = node.nonrel_inv->accept(*this);
      assert(nonrel_inv.original);
      assert(nonrel_inv.relaxed);
      debug_print("Pre body invariant: " + label);
      solver->push();
      if (!ignore_original) add_constraint(*nonrel_inv.original);
      add_checked_constraint(*inv.original && *nonrel_inv.relaxed);
      check();
      solver->pop();

      // Save current var version state
      assert(!h_var_version);
      h_var_version = new version_map(var_version);
      model_visitor->snapshot_vars();

      if (node.inf) {
        assert(!in_houdini);
        assert(node.houdini_invs.empty());
        assert(!cur_houdini_invs);
        assert(node.nonrel_houdini_invs.empty());
        assert(!cur_nonrel_houdini_invs);
        in_houdini = true;
        passed_houdini_pre = false;
        outer_h_unknown = false;

        // Eq template
        cur_houdini_invs = &node.houdini_invs;
        cur_nonrel_houdini_invs = &node.nonrel_houdini_invs;
        for (const std::pair<std::string, type_t>& kv : types) {
          if (!specvars.count(kv.first)) {
            // Leverage existing binop logic
            Var* v = new Var(kv.first);
            RelationalVar* ovar = new RelationalVar(ORIGINAL, v);
            RelationalVar* rvar = new RelationalVar(RELAXED, v);
            RelationalBoolExp* eq = new RelationalBoolExp(EQUALS, ovar, rvar);

            node.houdini_invs.push_back(eq);
          }
        }

        // Parent template
        if (parent_while) {
          parent_inf(parent_while->nonrel_inv, parent_while->inv);
        } else if (parent_function) {
          parent_inf(parent_function->requires, parent_function->r_requires);
        }

        do {
          if (outer_h_unknown) {
            debug_print("Houdini came up unknown, trying weak Houdini");
            std::vector<RelationalBoolExp*> old_h_invs(node.houdini_invs);
            std::vector<std::string> old_h_tmps(h_tmps);
            assert(old_h_invs.size() == old_h_tmps.size());
            std::vector<RelationalBoolExp*> new_h_invs;
            std::vector<std::string> new_h_tmps;

            std::vector<BoolExp*> old_nonrel_h_invs(node.nonrel_houdini_invs);
            std::vector<std::string> old_nonrel_h_tmps(nonrel_h_tmps);
            assert(old_nonrel_h_invs.size() == old_nonrel_h_tmps.size());
            std::vector<BoolExp*> new_nonrel_h_invs;
            std::vector<std::string> new_nonrel_h_tmps;

            node.nonrel_houdini_invs.clear();
            nonrel_h_tmps.clear();
            node.houdini_invs.clear();
            h_tmps.clear();
            weak_houdini(old_h_invs,
                         old_h_tmps,
                         node.houdini_invs,
                         h_tmps,
                         new_h_invs,
                         new_h_tmps,
                         node);

            weak_houdini(old_nonrel_h_invs,
                         old_nonrel_h_tmps,
                         node.nonrel_houdini_invs,
                         nonrel_h_tmps,
                         new_nonrel_h_invs,
                         new_nonrel_h_tmps,
                         node);

            node.houdini_invs = new_h_invs;
            h_tmps = new_h_tmps;
            node.nonrel_houdini_invs = new_nonrel_h_invs;
            nonrel_h_tmps = new_nonrel_h_tmps;
            houdini_failed = false;
            passed_houdini_pre = true;
          } else {
            debug_print("Trying Houdini invs: " + houdini_to_str());
            houdini_failed = false;
            node.accept(*this);
          }
        } while (houdini_failed);
        std::string houdinis = houdini_to_str(!node.seen);
        debug_print("Found Houdini invs: " + houdinis);

        in_houdini = false;
        cur_houdini_invs = nullptr;
        cur_nonrel_houdini_invs = nullptr;
      }
    }

    While* old_parent_while = parent_while;
    parent_while = &node;

    star_line();
    debug_print("While: " + label);

    // Verify houdini invariant
    bool h_unknown = false;
    // Use old version map *just* for precondition check in outer loop
    auto cur_var_version(var_version);
    if (&node.houdini_invs == cur_houdini_invs || !in_houdini) {
      var_version = *h_var_version;
      model_visitor->use_snapshot = true;
    }
    h_z3pair eqs = houdini_to_constraints(node);
    if (&node.houdini_invs == cur_houdini_invs || !in_houdini) {
      var_version = cur_var_version;
      model_visitor->use_snapshot = false;
    }
    if (!in_houdini) {
      delete h_var_version;
      h_var_version = nullptr;
    }
    if (!passed_houdini_pre || &node.houdini_invs != cur_houdini_invs) {
      debug_print("Pre body houdini: " + label);
      solver->push();
      add_constraint(*eqs.assumes);
      add_checked_constraint(*eqs.asserts);
      z3::check_result h_res =  check(!in_houdini);
      h_unknown = h_res == z3::unknown || h_unknown;
      solver->pop();

      weak_houdini_failed = weak_houdini_failed || h_res != z3::unsat;

      if (in_houdini) {
        parse_z3_model();
        if (houdini_failed || h_unknown) {
          if (h_unknown && &node.houdini_invs == cur_houdini_invs) {
            outer_h_unknown = true;
            houdini_failed = true;
          }
          parent_while = old_parent_while;
          return {nullptr, nullptr};
        }

        if (&node.houdini_invs == cur_houdini_invs) passed_houdini_pre = true;
      }
    }

    assert((in_houdini && !inv.original) ||
           (!in_houdini && inv.original));
    assert(!inv.relaxed);

    // Evaluate condition
    z3pair cond = node.cond->accept(*this);
    assert(cond.original);
    assert(cond.relaxed);

    z3::expr path_inv = *eqs.assumes && *eqs.asserts;
    inv = node.inv->accept(*this);
    nonrel_inv = node.nonrel_inv->accept(*this);
    path_inv = path_inv && *inv.original;
    if (!ignore_original) path_inv = path_inv && nonrel_inv.original;
    path_inv = path_inv && nonrel_inv.relaxed;
    std::array<z3::check_result, 3> paths;
    legal_path(*cond.original, *cond.relaxed, path_inv, node, paths);

    total_paths += 2;
    // Case 1: cond<o> && cond<r>
    switch (paths.at(0)) {
      case z3::unknown:
      case z3::sat:
        // Check both in lockstep
        debug_print(label + " : body cond<o> && cond<r>");
        h_unknown = check_loop(node, *cond.original && *cond.relaxed) || h_unknown;
        break;
      case z3::unsat:
        // All constraints implicitly true
        ++pruned_paths;
        break;
    }

    // Case 2: cond<o> && !cond<r>
    // Do nothing
    /*
    switch (paths.at(1)) {
      case z3::unknown:
      case z3::sat:
        {
          // Recheck cond
          solver->push();
          z3pair cond_new = node.cond->accept(*this);
          ++ignore_relaxed;
          debug_print(label + " : body cond<o> && !cond<r>");
          h_unknown = check_loop(node, *cond_new.original && !(*cond_new.relaxed)) || h_unknown;
          --ignore_relaxed;
          solver->pop();
        }
        break;
      case z3::unsat:
        // Do nothing
        break;
    }
    */

    // Case 3: !cond<o> && cond<r>
    switch (paths.at(2)) {
      case z3::unknown:
      case z3::sat:
        {
          // Recheck cond
          solver->push();
          z3pair cond_new = node.cond->accept(*this);
          ++ignore_original;
          debug_print(label + " : body !cond<o> && cond<r>");
          h_unknown = check_loop(node, !(*cond_new.original) && *cond_new.relaxed) || h_unknown;
          --ignore_original;
          solver->pop();
        }
        break;
      case z3::unsat:
        // Do nothing
        ++pruned_paths;
        break;
    }

    if (h_unknown && in_houdini && &node.houdini_invs == cur_houdini_invs) {
      outer_h_unknown = h_unknown;
      houdini_failed = true;
      parent_while = old_parent_while;
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
    inv = node.inv->accept(*this);
    nonrel_inv = node.nonrel_inv->accept(*this);
    assert(inv.original);
    assert(!inv.relaxed);
    assert(nonrel_inv.original);
    assert(nonrel_inv.relaxed);
    add_constraint(*inv.original);



    // TODO: Set vars in unrun vars to be equal to their old selves
    if (!prefixes.empty()) restore_unused_vars(old_versions, 0);

    if (ignore_original) restore_unused_vars(old_versions, 'r');
    else add_constraint(*nonrel_inv.original);

    add_constraint(*nonrel_inv.relaxed);




    if (!h_unknown) {
      eqs = houdini_to_constraints(node);
      add_constraint(*eqs.assumes);
      add_constraint(*eqs.asserts);
    }
    parent_while = old_parent_while;

    if (!in_houdini) {
      node.houdini_invs.clear();
      node.nonrel_houdini_invs.clear();
      node.seen = true;
    }
    return {nullptr, nullptr};
  }

  void CHLVisitor::restore_unused_vars(const version_map& old_versions,
                                       char ignore_type) {
    for (const std::pair<std::string, unsigned>& oldv : old_versions) {
      const std::string& name = oldv.first;
      const char& type = name.at(name.size() - 2);
      assert(type == 'r' || type == 'o' || type == 0);
      if (type == ignore_type) continue;

      const unsigned old_version = oldv.second;
      unsigned new_version = var_version.at(name);

      assert(old_version <= new_version);

      if (old_version < new_version) {
        std::string qname = name + "-" + std::to_string(old_version);
        if (vars.count(qname)) {
          // Dealing with a scalar
          z3::expr* old_var = vars.at(qname);
          z3::expr* new_var = get_current_var(name);
          assert(old_var);
          assert(new_var);
          assert(old_var != new_var);
          add_constraint(*old_var == *new_var, !ignore_type);
        } else {
          // Dealing with a vector
          z3::func_decl* old_vec = vectors.at(qname);
          z3::func_decl* new_vec = get_current_vec(name);
          assert(old_vec);
          assert(new_vec);
          assert(old_vec != new_vec);

          const dim_vec* dimensions = dim_map.at(name);
          assert(dimensions);
          assert(dimensions->size() == 1 || dimensions->size() == 2);

          z3::expr* constraint = vector_equals(*old_vec,
                                               *new_vec,
                                               *dimensions,
                                               dimensions->size() == 1 ?  IGNORE_1D : IGNORE_2D);
          add_constraint(*constraint, !ignore_type);
        }
      }
    }
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
    // TODO: Allow bad reads in copy nodes as well
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
    dim_vec* dimensions = dim_map.at(node.dest->name);
    assert(dimensions->size() == 1);

    z3::expr oforall = z3::forall(*forall_i, 0 <= (*src.original)(*forall_i));
    z3::expr rforall = z3::forall(*forall_i, 0 <= (*src.relaxed)(*forall_i));
    if (types.at(node.src->name) == UINT) {
      add_constraint(oforall);
      add_constraint(rforall);
    }

    z3::expr* oeq = vector_equals(*dest.original,
                                  *src.original,
                                  *dimensions,
                                  IGNORE_1D);


    z3::expr* req = nullptr;
    type_t dest_type = types.at(node.dest->name);
    if (regions.count(node.dest->name)) {
      // Generate a faulty write with the forall var
      z3::expr forall_src = (*src.relaxed)(*forall_i);
      z3::expr forall_dest = (*dest.relaxed)(*forall_i);
      model_visitor->prep_op(FWRITE, &forall_dest, &forall_src);
      model_visitor->var_equality = nullptr;
      z3::expr* inner = model_visitor->replace_op(dest_type, nullptr);
      if (!prefixes.empty()) {
        add_constraint(*model_visitor->var_equality, true);
      }

      // Use inner in a vec equals
      z3::expr bounds = (*forall_i >= context->int_val(0)) &&
                        (*forall_i < *dimensions->at(0).original);
      z3::expr eq = z3::implies(bounds, *inner);
      req = new z3::expr(z3::forall(*forall_i, eq));
    } else {
      req = vector_equals(*dest.relaxed,
                          *src.relaxed,
                          *dimensions,
                          IGNORE_1D);
    }
    assert(req);
    if (dest_type == UINT) {
      add_constraint(z3::implies(oforall, *oeq));
      add_constraint(z3::implies(rforall, *req));
    } else {
      add_constraint(*oeq);
      add_constraint(*req);
    }

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

  z3::expr* CHLVisitor::build_quantifier_var(const std::string& name,
                                             type_t type) {
    // Generate var names
    std::string oname = name + "<o>";
    std::string rname = name + "<r>";
    std::string tmp_base = "quantifier-tmp-" + std::to_string(quantifier_ctr);
    std::string otmp = tmp_base + "<o>";
    std::string rtmp = tmp_base + "<r>";
    ++quantifier_ctr;

    // Verify that this var does not exist
    assert(!contains_var(oname));
    assert(!contains_var(rname));

    // Add var
    // TODO: Support more than just ints
    add_var(type, otmp, rtmp);
    types[name] = type;
    specvars.insert(name);
    z3::expr* var = get_current_var(rtmp);
    assert(var);

    // Map var name to tmp var
    var_version[rname] = 0;
    vars[rname + "-0"] = var;
    var_version[oname] = 0;
    vars[oname + "-0"] = var;

    return var;
  }

  void CHLVisitor::destroy_quantifier_var(const std::string& name) {
    std::string oname = name + "<o>";
    std::string rname = name + "<r>";

    // Remove the quantifier var
    size_t res = var_version.erase(rname);
    assert(res);
    res = var_version.erase(oname);
    assert(res);
    res = vars.erase(rname + "-0");
    assert(res);
    res = vars.erase(oname + "-0");
    assert(res);
    res = types.erase(name);
    assert(res);
    res = specvars.erase(name);
    assert(res);

  }

  z3pair CHLVisitor::visit(RelationalForall &node) {
    assert(node.var);
    assert(node.exp);

    type_t type = node.type;
    z3::expr* var = build_quantifier_var(node.var->name,
                                         type == UINT ? INT : type);

    // Eval expression
    z3pair exp = node.exp->accept(*this);
    assert(exp.original);
    assert(!exp.relaxed);

    // Construct forall
    z3::expr* ret;
    switch (type) {
      case UINT:
        ret = new z3::expr(z3::forall(*var,
                                      z3::implies(0 <= *var, *exp.original)));
        break;
      case INT:
      case REAL:
        ret = new z3::expr(z3::forall(*var, *exp.original));
        break;
      case FLOAT:
      case BOOL:
        assert(false);
    }
    assert(ret);

    destroy_quantifier_var(node.var->name);

    expr_type = BOOL;

    return {ret, nullptr};
  }

  z3pair CHLVisitor::visit(RelationalExists &node) {
    assert(node.var);
    assert(node.exp);

    type_t type = node.type;
    z3::expr* var = build_quantifier_var(node.var->name,
                                         type == UINT ? INT : type);

    // Eval expression
    z3pair exp = node.exp->accept(*this);
    assert(exp.original);
    assert(!exp.relaxed);

    // Construct forall
    z3::expr* ret;
    switch (type) {
      case UINT:
        ret = new z3::expr(z3::exists(*var, *exp.original && 0 <= *var));
        break;
      case INT:
      case REAL:
        ret = new z3::expr(z3::exists(*var, *exp.original));
        break;
      case FLOAT:
      case BOOL:
        assert(false);
    }
    assert(ret);

    destroy_quantifier_var(node.var->name);

    expr_type = BOOL;

    return {ret, nullptr};
  }

  z3pair CHLVisitor::visit(Forall &node) {
    assert(node.var);
    assert(node.exp);

    type_t type = node.type;
    z3::expr* var = build_quantifier_var(node.var->name,
                                         type == UINT ? INT : type);

    // Eval expression
    z3pair exp = node.exp->accept(*this);
    assert(exp.original);
    assert(exp.relaxed);

    // Construct forall
    z3::expr *original = nullptr;
    z3::expr *relaxed = nullptr;
    switch (type) {
      case UINT:
        original = new z3::expr(z3::forall(*var, z3::implies(0 <= *var,
                                                             *exp.original)));
        relaxed = new z3::expr(z3::forall(*var, z3::implies(0 <= *var,
                                                            *exp.relaxed)));
        break;
      case INT:
      case REAL:
        original = new z3::expr(z3::forall(*var, *exp.original));
        relaxed = new z3::expr(z3::forall(*var, *exp.relaxed));
        break;
      case FLOAT:
      case BOOL:
        assert(false);
    }

    assert(original);
    assert(relaxed);

    destroy_quantifier_var(node.var->name);

    expr_type = BOOL;

    return {original, relaxed};
  }

  template<typename T>
  static void handle_h_removals(const assign_map& assignments,
                                std::vector<T>& invs,
                                std::vector<std::string>& tmps) {

    // Check which var eqs mapped to "false" and remove them
    assert(invs.size() == tmps.size());
    for (unsigned i = 0; i < tmps.size();) {
      std::string val = assignments.at(tmps.at(i));
      assert(val == "true" || val == "false");

      if (val == "false") {
        tmps.erase(tmps.begin() + i);
        invs.erase(invs.begin() + i);
      } else {
        ++i;
      }
    }

    assert(invs.size() == tmps.size());
  }

  void CHLVisitor::parse_z3_model() {
    if (houdini_failed || !z3_model || in_weak_houdini) return;

    houdini_failed = true;


    // Build up mapping of const assignments
    assign_map assignments;
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
    assert(cur_houdini_invs);
    assert(cur_nonrel_houdini_invs);
    handle_h_removals(assignments, *cur_houdini_invs, h_tmps);
    handle_h_removals(assignments, *cur_nonrel_houdini_invs, nonrel_h_tmps);
  }

  std::string CHLVisitor::houdini_to_str(bool count) {
    PrintVisitor pv(true);
    std::string ret = "";
    std::unordered_set<std::string> all_inferred;

    for (BoolExp* inv : *cur_nonrel_houdini_invs) {
      pv.output.clear();
      inv->accept(pv);
      ret += pv.output + ", ";
      if (count) all_inferred.insert(pv.output);
    }

    for (RelationalBoolExp* inv : *cur_houdini_invs) {
      pv.output.clear();
      inv->accept(pv);
      ret += pv.output + ", ";
      if (count) all_inferred.insert(pv.output);
    }

    if (count) num_inferred += all_inferred.size();

    ret += "\n";

    return ret;
  }

  z3pair CHLVisitor::visit(DeclareList& node) {
    assert(static_cast<bool>(node.car) ^ static_cast<bool>(node.mat_car));

    if (node.car) node.car->accept(*this);
    else node.mat_car->accept(*this);

    if (node.cdr) node.cdr->accept(*this);

    RETURN_VOID;
  }

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
  z3pair CHLVisitor::visit(Return& node) {
    // TODO:  Do something when we have function calls.
    RETURN_VOID;
  }
#pragma clang diagnostic pop

  z3pair CHLVisitor::visit(Function& node) {
    // TODO: This will need to be changed when we have function calls
    assert(!parent_function);
    parent_function = &node;

    // Declare vars
    assume_eq = false;
    node.decls->accept(*this);
    assume_eq = true;

    // Assume requirements
    z3pair requires = node.requires->accept(*this);
    assert(requires.original);
    assert(requires.relaxed);
    add_constraint(*requires.original);
    add_constraint(*requires.relaxed);

    // Leverage existing code for r_requires
    RelationalAssume r_requires_node(node.r_requires);
    r_requires_node.accept(*this);

    // Step into the body
    node.body->accept(*this);

    parent_function = nullptr;

    RETURN_VOID;
  }

  template <typename T>
  static void visit_property(T& node,
                             std::unordered_map<std::string, T*>& props) {
    const std::string& name = node.name->name;
    auto ret = props.emplace(name, &node);
    if (!ret.second) {
      std::cerr << "ERROR:  Property "
                << name
                << " already defined."
                << std::endl;
      exit(1);
    }
  }

  z3pair CHLVisitor::visit(Property& node) {
    visit_property(node, properties);

    RETURN_VOID;
  }

  z3pair CHLVisitor::visit(RelationalProperty& node) {
    visit_property(node, rel_properties);

    RETURN_VOID;
  }

  template<typename T, typename U>
  z3pair CHLVisitor::visit_property_application(T& node,
                                                std::unordered_map<std::string, U*>& props) {
    assert(substitutions.empty());

    const std::string& name = node.name->name;
    U* prop = nullptr;
    try {
      prop = props.at(name);
    } catch (const std::out_of_range&) {
      std::cerr << "ERROR: No such property: " << name << std::endl;
      exit(1);
    }
    assert(prop);

    VarList* app_head = node.args;
    DeclareList* prop_head = prop->decls;
    while (app_head && prop_head) {
      // TODO:  Type checking?
      // Build substitution map
      assert(static_cast<bool>(prop_head->car) ^
             static_cast<bool>(prop_head->mat_car));
      std::string key = prop_head->car ? prop_head->car->vars->car->name :
                                         prop_head->mat_car->vars->car->name;
      auto res = substitutions.emplace(key, app_head->car->name);

      if (!res.second) {
        std::cerr << "ERROR:  Parameter "
                  << key
                  << " is duplicated"
                  << std::endl;
        exit(1);
      }

      app_head = app_head->cdr;
      prop_head = prop_head->cdr;
    }
    if (app_head) {
      std::cerr << "ERROR:  Property application "
                << name
                << " has too many arguments."
                << std::endl;
      exit(1);
    }
    if (prop_head) {
      std::cerr << "ERROR:  Property application "
                << name
                << " has too few arguments."
                << std::endl;
      exit(1);
    }

    z3pair ret = prop->prop->accept(*this);

    substitutions.clear();
    expr_type = BOOL;

    return ret;
  }

  z3pair CHLVisitor::visit(PropertyApplication& node) {
    return visit_property_application(node, properties);
  }

  z3pair CHLVisitor::visit(RelationalPropertyApplication& node) {
    return visit_property_application(node, rel_properties);
  }

  z3pair CHLVisitor::visit(SpecPropertyApplication& node) {
    // Snapshot vars and spec var map
    std::unordered_map<std::string, z3::expr*> old_vars(vars);
    std::unordered_map<std::string, z3::func_decl*> old_vectors(vectors);
    std::unordered_set<std::string> old_specvars(specvars);

    VarList* vl_head = nullptr;
    VarList* vl_tail = nullptr;
    for (RelationalVarList* head = node.args; head; head = head->cdr) {
      const RelationalVar& v = *head->car;
      const std::string& name = v.var->name;

      if (!vl_head) {
        vl_head = new VarList(v.var, nullptr);
        vl_tail = vl_head;
      } else {
        vl_tail->cdr = new VarList(v.var, nullptr);
        vl_tail = vl_tail->cdr;
      }

      // Mark as a specvar
      specvars.insert(name);

      // Duplicate both executions to match var<relation>
      std::string oname = name + "<o>";
      std::string rname = name + "<r>";

      oname = get_current_var_name(oname);
      rname = get_current_var_name(rname);
      assert(!oname.empty());
      assert(!rname.empty());

      if (vars.count(oname)) {
        z3::expr* ovar = vars.at(oname);
        z3::expr* rvar = vars.at(rname);

        if (v.relation == ORIGINAL) vars[rname] = ovar;
        else vars[oname] = rvar;
      } else {
        z3::func_decl* ovec = vectors.at(oname);
        z3::func_decl* rvec = vectors.at(rname);

        if (v.relation == ORIGINAL) vectors[rname] = ovec;
        else vectors[oname] = rvec;
      }
    }

    RelationalPropertyApplication prop(node.name, vl_head);
    z3pair ret = prop.accept(*this);

    // Restore
    vars = old_vars;
    vectors = old_vectors;
    specvars = old_specvars;

    return ret;
  }
}


