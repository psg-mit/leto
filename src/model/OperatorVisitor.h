#pragma once

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <z3++.h>
// From https://github.com/Z3Prover/z3/pull/218
namespace z3 {
  expr implies(expr const & a, expr const & b);
}

#include "ModelNodes.h"
#include "Z3Visitor.h"

namespace model {
  class OperatorVisitor : public Z3Visitor {
    public:
      OperatorVisitor(z3::expr* arg1_subst,
                      z3::expr* arg2_subst,
                      z3::expr* result_subst,
                      var_map* vars_,
                      version_map* var_version_,
                      z3::context* context,
                      z3::solver* solver,
                      type_t expr_type_,
                      const std::unordered_set<std::string> *updated_,
                      const std::unordered_map<std::string, type_t>& types);
      virtual z3::expr* visit(const Var &node) override;
      virtual z3::expr* visit(const Operator &node) override;
      virtual z3::expr* visit(const Old& node);

      // Inherited
      /*
      virtual z3::expr* visit(const Bool &node);
      virtual z3::expr* visit(const Int &node);
      virtual z3::expr* visit(const BinOp &node) override;
      virtual z3::expr* visit(const BoolBinOp &node) override;
      */

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
      virtual z3::expr* visit(const StatementList &node) { assert(false); }
      virtual z3::expr* visit(const Declare &node) { assert(false); }
      virtual z3::expr* visit(const Assign &node) { assert(false); }
      virtual z3::expr* visit(const Block &node) { assert(false); }
#pragma clang diagnostic pop

      z3::expr* when;
      bool no_guard;

    private:
      z3::context* context;
      z3::solver* solver;
      var_map* vars;
      version_map* var_version;
      std::unordered_map<std::string, z3::expr*> substitutions;
      bool in_ensures;
      const std::unordered_set<std::string> *updated;
      type_t expr_type;

      z3::expr* get_current_var(const std::string& name) const;
      z3::expr* get_prev_var(const std::string& name) const;
      z3::expr* get_set_var(const std::string& name) const;
  };
}
