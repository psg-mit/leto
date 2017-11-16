#include "OperatorVisitor.h"
#include "Z3Visitor.h"

namespace model {
  void Z3Visitor::BuildOp(operator_t op_type,
                          Var* op_arg1,
                          Var* op_arg2,
                          Var* result,
                          Bool* when) {
    BinOp *oop = new BinOp(op_type, op_arg1, op_arg2);
    BoolBinOp *ensures = new BoolBinOp(EQUALS, result, oop);
    Operator* op_oop = new Operator(op_type,
                                    op_arg1,
                                    op_arg2,
                                    when,
                                    nullptr,
                                    ensures);
    op_mods.emplace(op_type, new std::unordered_set<std::string>());
    ops.emplace(op_type, std::vector<const Operator*>());
    ops.at(op_type).push_back(op_oop);
  }

  Z3Visitor::Z3Visitor(z3::context* context_,
                       z3::solver* solver_,
                       type_t expr_type_) {

    context = context_;
    solver = solver_;
    expr_type = expr_type_;
    arg1 = arg2 = nullptr;

    // Build reliable operators
    Var *op_arg1 = new Var(ARG1_STR);
    Var *op_arg2 = new Var(ARG2_STR);
    Var *result = new Var(RESULT_STR);
    Bool *when = new Bool(true);
    BuildOp(OMINUS, op_arg1, op_arg2, result, when);
    BuildOp(OPLUS, op_arg1, op_arg2, result, when);
    BuildOp(OTIMES, op_arg1, op_arg2, result, when);
    BuildOp(ODIV, op_arg1, op_arg2, result, when);

    current_mods = nullptr;
    use_snapshot = false;
    frame = "";
    var_equality = nullptr;
    begin_commit = nullptr;
    end_commit = nullptr;
  }

  z3::expr* Z3Visitor::get_current_var(const std::string& name) {
    unsigned version = UINT_MAX;
    if (!frame.empty()) {
        version = frames.at(frame).at(name);
        frame = "";
    } else if (use_snapshot) version = snapshot.at(name);
    else version = var_version.at(name);
    return vars.at(name + "-" + std::to_string(version));
  }

  z3::expr* Z3Visitor::get_previous_var(const std::string& name) {
    unsigned version = use_snapshot ? snapshot.at(name) : var_version.at(name);
    assert(version);
    return vars.at(name + "-" + std::to_string(version - 1));
  }

  z3::expr* Z3Visitor::get_var_at(const std::string& name, unsigned version) {
    return vars.at(name + "-" + std::to_string(version));
  }

  type_t Z3Visitor::get_var_type(const std::string& name) {
    return types.at(name);
  }

  z3::expr* Z3Visitor::visit(const Declare &node) {
    // TODO: Take type into account
    assert(node.var->name != ARG1_STR);
    assert(node.var->name != ARG2_STR);
    assert(node.var->name != RESULT_STR);

#ifndef NDEBUG
    size_t start_size = vars.size();
    size_t start_version_size = var_version.size();
#endif

    // Declare var
    const std::string &name = node.var->name + "-0";
    z3::expr* var = nullptr;
    switch (node.type) {
      case BOOL:
        var = new z3::expr(this->context->bool_const(name.c_str()));
        break;
      case INT:
        var = new z3::expr(this->context->int_const(name.c_str()));
        break;
      case REAL:
        var = new z3::expr(this->context->real_const(name.c_str()));
        break;
      case FLOAT:
      case UINT:
        assert(false);
    }
    vars[name] = var;
    var_version[node.var->name] = 0;
    types[node.var->name] = node.type;

    assert(vars.size() == start_size + 1);
    assert(var_version.size() == start_version_size + 1);

    return nullptr;
  }

  z3::expr* Z3Visitor::visit(const Assign &node) {
    // TODO: Allow redefinition
    // Get both pairs
    z3::expr* lhs = node.lhs->accept(*this);
    z3::expr* rhs = node.rhs ->accept(*this);

    assert(lhs);
    assert(rhs);

    // Set LHS == RHS
    solver->add(*lhs == *rhs);

    return nullptr;
  }

  z3::expr* Z3Visitor::visit(const Var &node) {
    return get_current_var(node.name);
  }

  z3::expr* Z3Visitor::visit(const Old& node) {
    return get_previous_var(node.var->name);
  }

  z3::expr* Z3Visitor::visit(const Bool &node) {
    z3::expr* res = new z3::expr(context->bool_val(node.value));

    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const Int &node) {
    z3::expr* res = new z3::expr(context->int_val(node.value));

    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const Real &node) {
    assert(node.denominator);
    z3::expr* res = new z3::expr(context->real_val(node.numerator,
                                                   node.denominator));

    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const Float &node) {
    z3::expr* res = float_val(context, node.value);
    expr_type = FLOAT;
    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const StatementList &node) {
    node.lhs->accept(*this);
    node.rhs->accept(*this);

    return nullptr;
  }

  z3::expr* Z3Visitor::visit(const BinOp &node) {
    // Get both pairs
    z3::expr* lhs = node.lhs->accept(*this);
    z3::expr* rhs = node.rhs->accept(*this);
    assert(lhs);
    assert(rhs);

    // Build relational pairs
    z3::expr *res = binop(context, node.op, expr_type, lhs, rhs);

    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const BoolBinOp &node) {
    // Get both pairs
    z3::expr* lhs = node.lhs->accept(*this);
    z3::expr* rhs = node.rhs->accept(*this);
    assert(lhs);
    assert(rhs);

    // Build relational pairs
    z3::expr *res = nullptr;
    switch (node.op) {
      case EQUALS:
        res = new z3::expr(*lhs == *rhs);
        break;
      case AND:
        res = new z3::expr(*lhs && *rhs);
        break;
      case OR:
        res = new z3::expr(*lhs || *rhs);
        break;
      case LT:
        res = new z3::expr(*lhs < *rhs);
        break;
      case LTEQ:
        res = new z3::expr(*lhs <= *rhs);
        break;
      case XOR:
        assert(false);
    }

    assert(res);
    return res;
  }

  z3::expr* Z3Visitor::visit(const Operator &node) {
    assert(node.arg1->name == ARG1_STR);
    assert((node.op == FREAD) ^ (node.arg2 && node.arg2->name == ARG2_STR));
    assert(!current_mods);

    // Save this snippet of the tree for later
    if (!ops.count(node.op)) {
      ops.emplace(node.op, std::vector<const Operator*>());
    }
    ops.at(node.op).push_back(&node);

    // Track modified model vars
    if (!op_mods.count(node.op)) {
      op_mods.emplace(node.op, new std::unordered_set<std::string>);
    }
    if (node.modifies) {
      current_mods = op_mods.at(node.op);
      node.modifies->accept(*this);
      current_mods = nullptr;
    }

    return nullptr;
  }

  z3::expr* Z3Visitor::visit(const VarList &node) {
    if (node.car) {
      current_mods->insert(node.car->name);
      if (node.cdr) node.cdr->accept(*this);
    }
    return nullptr;
  }

  z3::expr* Z3Visitor::visit(const Commit& node) {
    switch (node.type) {
      case BEGIN:
        if (begin_commit) ERROR("begin_commit already defined");
        begin_commit = &node;
        break;
      case END:
        if (end_commit) ERROR("end_commit already defined");
        end_commit = &node;
        break;
      default:
        assert(false);
    }
    return nullptr;
  }

  void Z3Visitor::prep_op(operator_t op_, z3::expr* arg1_, z3::expr* arg2_) {
    assert(arg1_);
    assert((op_ == FREAD) ^ (arg2_ != nullptr));

    arg1 = arg1_;
    arg2 = arg2_;
    op = op_;
  }

  bool Z3Visitor::prepped() {
    if (op == FREAD) {
      return arg1;
    }

    assert((arg1 && arg2) ^ (!arg1 && !arg2));
    return arg1 && arg2;
  }

  void Z3Visitor::unprep() {
    arg1 = arg2 = nullptr;
  }

  z3::expr* Z3Visitor::replace_op(type_t type, z3::expr* res) {
    expr_type = type;
    assert(arg1);
    assert((op == FREAD) ^ (arg2 != nullptr));
    assert(ops.count(op));
    const std::vector<const Operator*>& impls = ops.at(op);
    assert(!impls.empty());

    // Track old versions
    version_map old_versions(var_version);

    // Substitute and OR operators together
    updated = op_mods.at(op);
    OperatorVisitor subst(arg1,
                          arg2,
                          res,
                          &vars,
                          &var_version,
                          context,
                          solver,
                          expr_type,
                          updated,
                          types);
    const Operator* impl = impls.at(0);
    assert(impl);
    z3::expr* fn = impl->accept(subst);
    for (size_t i = 1; i < impls.size(); ++i) {
      impl = impls.at(i);
      assert(impl);
      z3::expr* part = impl->accept(subst);
      *fn = *fn || *part;
    }

    // Build equality with old versions
    assert(old_versions.size() == var_version.size());
    assert(!var_equality);
    var_equality = new z3::expr(context->bool_val(true));
    for (const std::pair<std::string, unsigned>& old_var : old_versions) {
      const std::string& vname = old_var.first;
      const unsigned old_version = old_var.second;
      if (old_version != var_version.at(vname)) {
        z3::expr* old = get_var_at(vname, old_version);
        z3::expr* cur = get_current_var(vname);

        *var_equality = *var_equality && *old == *cur;
      }
    }


    arg1 = arg2 = nullptr;
    return fn;
  }

  void Z3Visitor::check() {
    /*
    // Build functions
    for (const std::pair<operator_t, std::vector<z3::expr*>> &op : ops) {
      const std::string &name = FN_NAMES.at(op.first);
      const std::vector<z3::expr*> &bodies = op.second;

      // OR operators together
      z3::expr body = *bodies.at(0);
      for (size_t i = 1; i < bodies.size(); ++i) {
        body = body || bodies.at(i);
      }

      // Emit constraint
      // TODO: Make this work for more than just ints
      context.function(name.c_str(),
                       context.int_sort(),
                       context.int_sort(),
                       context.int_sort());
    }
    */
    std::cout << *solver << std::endl;
  }

  void Z3Visitor::snapshot_vars() {
    snapshot = var_version;
  }

  void Z3Visitor::add_frame(const  std::string& name) {
    frames[name] = var_version;
  }
}
