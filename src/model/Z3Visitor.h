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

#include "../common.h"

#include "../lang/CHLVisitor.h"

#include "ModelNodes.h"
#include "ASTVisitor.h"

#define POWERON_VAR_NAME "exn-poweron"

// CHLVisitor forward declaration
namespace lang {
  class CHLVisitor;
}

namespace model {

  typedef std::unordered_map<std::string, z3::expr*> var_map;

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
      virtual z3::expr* visit(const Commit &node);
      virtual z3::expr* visit(const Step &node);

      void prep_op(operator_t op, z3::expr* arg1_, z3::expr* arg2_);
      bool prepped();
      void unprep();
      z3::expr* replace_op(type_t type, z3::expr* res);
      z3::expr* get_current_var(const std::string& name);
      z3::expr* get_previous_var(const std::string& name);
      type_t get_var_type(const std::string& name);

      void snapshot_vars();

      bool has_user_step();

      void add_frame(const std::string& name);
      std::string frame;

      z3::expr* commit(commit_t type);
      z3::expr* step();

      void set_chl(lang::CHLVisitor* chl);

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
      virtual z3::expr* visit(const Block &node) { assert(false); }
#pragma clang diagnostic pop

      bool use_snapshot;

      z3::expr* var_equality;


    protected:
      std::unordered_set<std::string>* current_mods;
      lang::CHLVisitor* chl;

    private:
      z3::context* context;
      z3::solver* solver;
      var_map vars;
      std::unordered_map<std::string, type_t> types;
      version_map var_version;
      version_map snapshot;
      std::map<operator_t, std::vector<const Operator*>> ops;
      std::map<operator_t, std::unordered_set<std::string>*> op_mods;
      std::map<commit_t, std::unordered_set<std::string>*> commit_mods;
      std::map<std::string, version_map> frames;
      z3::expr* get_var_at(const std::string& name, unsigned version);
      std::vector<const Step*> steps;
      std::unordered_set<std::string> exception_mods;

      operator_t op;
      z3::expr* arg1;
      z3::expr* arg2;
      type_t expr_type;

      const Commit* begin_commit;
      const Commit* end_commit;


      void BuildOp(operator_t op,
                   Var* op_arg1,
                   Var* op_arg2,
                   Var* result,
                   Bool* when);

      void add_var(const std::string& name, type_t type);
      bool var_exists(const std::string& name);

  };
}
