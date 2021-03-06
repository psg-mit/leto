#pragma once

#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <z3++.h>
// From https://github.com/Z3Prover/z3/pull/218
namespace z3 {
  expr implies(expr const & a, expr const & b);
}

#include "../common.h"
#include "ModelNodes.h"
#include "ASTVisitor.h"

namespace model {

  typedef std::unordered_map<std::string, z3::expr*> var_map;

  struct op_sub {
    std::unique_ptr<z3::expr> when_disjunction;
    z3::expr* subst;
    bool trivially_not_stuck;
  };

  class Z3Visitor : public ASTVisitor {
    public:
      const std::unordered_set<std::string>* updated;

      Z3Visitor(z3::context* context_,
                z3::solver* solver_,
                type_t expr_type_=INT);
      virtual z3::expr* visit(const Declare &node);
      virtual z3::expr* visit(const Assign &node);
      virtual z3::expr* visit(const Var &node);
      virtual z3::expr* visit(const Bool &node);
      virtual z3::expr* visit(const StatementList &node);
      virtual z3::expr* visit(const Int &node);
      virtual z3::expr* visit(const Float &node);
      virtual z3::expr* visit(const BinOp &node);
      virtual z3::expr* visit(const BoolBinOp &node);
      virtual z3::expr* visit(const Operator &node);
      virtual z3::expr* visit(const VarList &node);
      virtual z3::expr* visit(const Old &node);
      virtual z3::expr* visit(const Real &node);

      void prep_op(operator_t op, z3::expr* arg1_, z3::expr* arg2_);
      bool prepped();
      void unprep();
      op_sub replace_op(type_t type, z3::expr* res);
      z3::expr* get_current_var(const std::string& name);
      z3::expr* get_previous_var(const std::string& name);
      type_t get_var_type(const std::string& name);
      z3::expr* add_var(std::string name);
      void remove_refined();

      void check();

      void snapshot_vars();

      void add_frame(const std::string& name);
      std::string frame;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
      virtual z3::expr* visit(const Block &node) { assert(false); }
#pragma clang diagnostic pop

      bool use_snapshot;

      void init_vars();

      z3::expr* var_equality;
      z3::solver* solver;

    protected:
      std::unordered_set<std::string>* current_mods;

    private:
      z3::context* context;
      var_map vars;
      std::unordered_map<std::string, type_t> types;
      version_map var_version;
      version_map snapshot;
      std::map<operator_t, std::vector<const Operator*>> ops;
      std::map<operator_t, std::unordered_set<std::string>*> op_mods;
      std::map<std::string, version_map> frames;
      std::unordered_set<size_t> refined;
      z3::expr* get_var_at(const std::string& name, unsigned version);

      operator_t op;
      z3::expr* arg1;
      z3::expr* arg2;
      type_t expr_type;
      std::unordered_map<std::string, z3::expr> initializations;
      size_t tmp_count;



      void BuildOp(operator_t op,
                   Var* op_arg1,
                   Var* op_arg2,
                   Var* result,
                   Bool* when);
  };
}
