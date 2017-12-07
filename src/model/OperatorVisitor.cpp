#include "OperatorVisitor.h"

namespace model {
  OperatorVisitor::OperatorVisitor(z3::expr* arg1_subst,
                                   z3::expr* arg2_subst,
                                   z3::expr* result_subst,
                                   var_map* vars_,
                                   version_map* var_version_,
                                   z3::context* context_,
                                   z3::solver* solver_,
                                   type_t expr_type_,
                                   const std::unordered_set<std::string> *updated_,
                                   const std::unordered_map<std::string, type_t>& types)
      : Z3Visitor(context_, solver_, expr_type_),
        vars(vars_),
        var_version(var_version_) {
    substitutions[ARG1_STR] = arg1_subst;
    substitutions[ARG2_STR] = arg2_subst;
    substitutions[RESULT_STR] = result_subst;

    context = context_;
    solver = solver_;
    expr_type = expr_type_;
    updated = updated_;

    // Update all modified vars
    for (const std::string& name : *updated) {
      // Intialize next version
      unsigned next_version = ++var_version->at(name);
      const std::string &new_name = name + "-" + std::to_string(next_version);
      z3::expr *var = nullptr;
      switch (types.at(name)) {
        case BOOL:
          var = new z3::expr(context->bool_const(new_name.c_str()));
          break;
        case INT:
        case UINT:
          var = new z3::expr(context->int_const(new_name.c_str()));
          break;
        case REAL:
          var = new z3::expr(context->real_const(new_name.c_str()));
          break;
        case FLOAT:
          assert(false);
      }
      (*vars)[new_name] = var;
    }

    in_ensures = false;

    assert(substitutions.size() == 3);
  }

  z3::expr* OperatorVisitor::visit(const Var &node) {
    const std::string& name = node.name;
    if (substitutions.count(name)) return substitutions.at(name);

    if (in_ensures) {
      return get_current_var(name);
    } else {
      return updated->count(name) ? get_prev_var(name) : get_current_var(name);
    }
  }

  z3::expr* OperatorVisitor::visit(const Old& node) {
    return get_prev_var(node.var->name);
  }

  z3::expr* OperatorVisitor::visit(const Operator &node) {
    assert(!current_mods);
    z3::expr* when = node.when->accept(*this);
    current_mods = new std::unordered_set<std::string>();
    if (node.modifies) node.modifies->accept(*this);
    in_ensures = true;
    z3::expr* ensures = node.ensures->accept(*this);
    in_ensures = false;
    assert(when);
    assert(ensures);

    z3::expr assertion = *when && *ensures;

    // Figure out which model vars were unmodified
    std::unordered_set<std::string> unmodified(*updated);
    for (const std::string& modified : *current_mods) {
      size_t res = unmodified.erase(modified);
      assert(res);
    }

    // Mark new unmodified vars as equivalent to old ones
    for (const std::string& var : unmodified) {
      z3::expr* cur = get_current_var(var);
      z3::expr* prev = get_prev_var(var);
      assert(cur);
      assert(prev);
      assert(cur != prev);

      assertion = assertion && (*cur == *prev);
    }

    z3::expr* ret = new z3::expr(assertion);

    delete current_mods;
    current_mods = nullptr;

    return ret;
  }

  z3::expr* OperatorVisitor::visit(const Commit& node) {
    in_ensures = true;
    z3::expr* ensures = node.ensures->accept(*this);
    assert(ensures);
    in_ensures = false;

    return ensures;
  }

  z3::expr* OperatorVisitor::visit(const Step& node) {
    z3::expr* when = node.when->accept(*this);
    in_ensures = true;
    z3::expr* ensures = node.ensures->accept(*this);
    in_ensures = false;
    assert(when);
    assert(ensures);

    z3::expr assertion = *when && *ensures;

    // TODO: Exception handling code will have to be updated when there is more
    // than one possible exception type
    assert(updated);
    assert(updated->empty() || updated->size() == 1);
    z3::expr* cur_exn = get_current_var(POWERON_VAR_NAME);
    switch (node.throws) {
      case NONE:
        if (updated->size() == 1) {
          // Set exn state to be equal to old exn state
          z3::expr* prev = get_prev_var(POWERON_VAR_NAME);
          assertion = assertion && (*cur_exn == *prev);
        }
        break;
      case POWERON:
        assertion = assertion && cur_exn;
        break;
    }

    z3::expr* ret = new z3::expr(assertion);
    assert(ret);
    return ret;
  }

  z3::expr* OperatorVisitor::get_current_var(const std::string& name) const {
    return vars->at(name + "-" + std::to_string(var_version->at(name)));
  }

  z3::expr* OperatorVisitor::get_set_var(const std::string& name) const {
    return vars->at(name + "-" + std::to_string(var_version->at(name)) + "-set");
  }

  z3::expr* OperatorVisitor::get_prev_var(const std::string& name) const {
    unsigned version = var_version->at(name);
    assert(version);
    --version;
    return vars->at(name + "-" + std::to_string(version));
  }
}
