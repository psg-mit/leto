#pragma once

#include <fstream>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include <z3++.h>
// From https://github.com/Z3Prover/z3/pull/218
namespace z3 {
  expr implies(expr const & a, expr const & b);
}

#include "../common.h"
#include "LangNodes.h"
#include "ASTVisitor.h"

#include "../model/Z3Visitor.h"

struct vec_pair {
  z3::func_decl* original;
  z3::func_decl* relaxed;
};

namespace lang {
  typedef std::vector<z3pair> dim_vec;

  class CHLVisitor : public ASTVisitor {
    public:
      CHLVisitor(z3::context* context_,
                 z3::solver* solver_,
                 model::Z3Visitor* model_visitor_,
                 std::ofstream& z3_log_,
                 std::ofstream& smt2_log_);
      virtual z3pair visit(StatementList &node) override;
      virtual z3pair visit(Var &node) override;
      virtual z3pair visit(Assign &node) override;
      virtual z3pair visit(Declare &node) override;
      virtual z3pair visit(BoolExp &node) override;
      virtual z3pair visit(RelationalVar &node) override;
      virtual z3pair visit(SpecVar &node) override;
      virtual z3pair visit(BinOp &node) override;
      virtual z3pair visit(RelationalBoolExp &node) override;
      virtual z3pair visit(RelationalNormal &node) override;
      virtual z3pair visit(RelationalBinOp &node) override;
      virtual z3pair visit(RelationalInt &node) override;
      virtual z3pair visit(RelationalBool &node) override;
      virtual z3pair visit(Bool &node) override;
      virtual z3pair visit(Int &node) override;
      virtual z3pair visit(ArrayAccess &node) override;
      virtual z3pair visit(RelationalArrayAccess &node) override;
      virtual z3pair visit(SpecArrayAccess &node) override;
      virtual z3pair visit(If &node) override;
      virtual z3pair visit(While &node) override;
      virtual z3pair visit(Float &node) override;
      virtual z3pair visit(RelationalFloat &node) override;
      virtual z3pair visit(Real &node) override;
      virtual z3pair visit(RelationalReal &node) override;
      virtual z3pair visit(DeclareMat &node) override;
      virtual z3pair visit(DeclareLMat &node) override;
      virtual z3pair visit(ModelDeref &node) override;
      virtual z3pair visit(RelationalModelDeref &node) override;
      virtual z3pair visit(Skip &node) override;
      virtual z3pair visit(Assert &node) override;
      virtual z3pair visit(RelationalAssume &node) override;
      virtual z3pair visit(RelationalAssert &node) override;
      virtual z3pair visit(Fail &node) override;
      virtual z3pair visit(Copy &node) override;
      virtual z3pair visit(Exponent &node) override;
      virtual z3pair visit(ExprList &node) override;
      virtual z3pair visit(ArrayAssign &node) override;
      virtual z3pair visit(RelationalForall &node) override;
      virtual z3pair visit(FaultyRead &node) override;
      virtual z3pair visit(FaultyWrite &node) override;

      z3::check_result check(bool exit_on_sat=true);
      int get_errors() { return errors; }

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
      virtual z3pair visit(Block &node) override {assert(false);}
      virtual z3pair visit(VarList &node) override {assert(false);}
#pragma clang diagnostic pop

      bool unsat_context;
      bool unknown_context;
      size_t constraints_generated;
    private:
      z3::context* context;
      z3::solver* solver;
      std::unordered_map<std::string, z3::expr*> vars;
      version_map var_version;
      version_map* h_var_version;
      model::Z3Visitor* model_visitor;
      std::unordered_map<std::string, z3::func_decl*> vectors;
      bool in_assign;
      int errors;
      std::unordered_map<std::string, type_t> types;
      std::unordered_set<std::string> specvars;
      std::unordered_map<std::string, dim_vec*> dim_map;
      std::unordered_map<std::string, std::vector<int>*> light_dim_map;
      std::unordered_set<std::string> light_mats;
      type_t expr_type;
      vec_pair last_array;
      std::vector<Expression*> virtual_vec;
      std::vector<int>* last_light_dim;
      dim_vec* last_dim;
      unsigned while_count;
      unsigned ignore_original;
      unsigned ignore_relaxed;
      z3::expr* old_o;
      z3::expr* old_r;
      std::vector<z3::expr*> prefixes;
      std::ofstream& z3_log;
      std::ofstream& smt2_log;
      const std::string* last_base_name;
      z3::expr* forall_i;
      z3::expr* forall_j;
      unsigned forall_ctr;
      bool in_houdini;
      bool houdini_failed;
      z3::model* z3_model;
      size_t h_tmp;
      bool passed_houdini_pre;
      bool outer_h_unknown;
      bool inner_h_unknown;
      While* parent_while;

      // Contains *unqualified* vars to be set equal to eachother
      std::vector<RelationalBoolExp*>* cur_houdini_invs;
      std::vector<std::string> h_tmps;

      z3pair add_var(type_t type, std::string oname, std::string rname);
      vec_pair add_vector(type_t type,
                          const std::string& oname,
                          const std::string& rname,
                          const dim_vec& dimensions);
      void add_constraint(const z3::expr& constraint, bool invert_last=false);
      z3::expr* get_current_var(std::string name);
      z3::func_decl* get_current_vec(std::string name);
      z3::expr* make_float(const std::string& name);
      bool contains_var(std::string name);

      /**
       * Returns true if houdini was unknown
       */
      bool check_loop(While &node, z3::expr cond);

      z3::expr* get_previous_var(std::string name);
      void push_prefix(z3::expr* prefix);
      void pop_prefix();
      void if_same(z3::expr original, z3::expr relaxed, Statement* body);
      void if_diff(z3::expr original,
                   z3::expr relaxed,
                   Statement* obody,
                   Statement* rbody);
      void add_checked_constraint(const z3::expr& constraint);
      z3::expr get_constraint(const z3::expr& constraint, bool invert_last);
      z3::expr* light_mat_elem_eq(Var& lhs_elem_v,
                                  Var& rhs_elem_v,
                                  RelationalVar& lhs_rv,
                                  RelationalVar& rhs_rv);
      void check_context();
      void legal_path(z3::expr& original,
                      z3::expr& relaxed,
                      z3::expr& inv,
                      const While& node,
                      std::array<z3::check_result, 3>& results);

      /**
       * Sets two vectors equal (except at ignore_index) without the use of
       * quantifiers.
       *
       * If you would not like to ignore a position, set ignore_index to be
       * full of nullptr
       */
      z3::expr* vector_equals(z3::func_decl& x,
                              z3::func_decl& y,
                              const dim_vec& dimensions,
                              std::vector<z3::expr*>& ignore_index);

      z3::expr* houdini_to_constraints(const While& node);


      /**
       * Parses z3_model and modifies houdini_vars accordingly
       *
       * Sets houdini_failed to true if a z3 model exists, indicating an
       * invalid set of houdini_vars
       */
      void parse_z3_model();

      std::string houdini_to_str();
  };
}
