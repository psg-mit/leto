#pragma once
#include <string>
#include <vector>

#include <z3++.h>

#include "../common.h"


/*
 * TODO: Functions, vectors, tuples, conditionals, bools, assertions
 */

namespace lang {

  enum bool_t {AND, EQUALS, NEQ, LT, XOR, IMPLIES, OR, LTEQ};
  enum relation_t {ORIGINAL, RELAXED};

  class ASTVisitor;

  struct z3pair {
    z3::expr *original;
    z3::expr *relaxed;
  };

  class LangNode {
    public:
      virtual z3pair accept(ASTVisitor &visitor)  = 0;
      virtual ~LangNode () {}
  };

  class Expression : public LangNode { };
  class RelationalExp : public Expression {};

  class Int : public Expression {
    public:
      Int(int value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      int value;
  };

  class RelationalInt : public RelationalExp {
    public:
      RelationalInt(int value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      int value;
  };

  class RelationalBool : public RelationalExp {
    public:
      RelationalBool(bool value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      bool value;
  };

  class Bool : public  Expression {
    public:
      Bool(bool value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      bool value;
  };

  class Float : public Expression {
    public:
      Float(float value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      float value;
  };

  class RelationalFloat : public RelationalExp {
    public:
      RelationalFloat(float value_) : value(value_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      float value;
  };

  class Real : public Expression {
    public:
      Real(int numerator_, int denominator_) :
          numerator(numerator_), denominator(denominator_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      int numerator;
      int denominator;
  };

  class RelationalReal : public RelationalExp {
    public:
      RelationalReal(int numerator_, int denominator_) :
          numerator(numerator_), denominator(denominator_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      int numerator;
      int denominator;
  };

  class Var : public Expression {
    public:
      Var(const std::string &name_) : name(name_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      std::string name;
  };

  class VarList : public Expression {
    public:
      VarList(Var *car_, VarList *cdr_) : car(car_), cdr(cdr_) {}
      VarList(Var *car_,
              std::vector<Expression*> dimensions_,
              VarList *cdr_) : car(car_), dimensions(dimensions_), cdr(cdr_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* car;
      std::vector<Expression*> dimensions;
      VarList* cdr;
  };

  class RelationalVar : public RelationalExp {
    public:
      RelationalVar(relation_t relation_, Var *var_, bool check_spec_=true) :
          relation(relation_), var(var_), check_spec(check_spec_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      relation_t relation;
      Var* var;
      bool check_spec;
  };

  class RelationalVarList : public RelationalExp {
    public:
      RelationalVarList(RelationalVar *car_, RelationalVarList *cdr_) :
          car(car_), cdr(cdr_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      RelationalVar* car;
      RelationalVarList* cdr;
  };


  class SpecVar : public RelationalExp {
    public:
      SpecVar(Var *var_) : var(var_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* var;
  };

  class BinOp : public Expression {
    public:
      BinOp(operator_t op_, Expression *lhs_, Expression *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      operator_t op;
      Expression* lhs;
      Expression* rhs;
  };

  class FaultyRead : public Expression {
    public:
      FaultyRead(Expression* var_) :
          var(var_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Expression* var;
  };

  class Exponent : public Expression {
    public:
      Exponent(Expression *base_, Expression *exp_) :
          base(base_), exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Expression* base;
      Expression* exp;
  };

  class RelationalBinOp : public RelationalExp {
    public:
      RelationalBinOp(operator_t op_,
            RelationalExp *lhs_,
            RelationalExp *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      operator_t op;
      RelationalExp* lhs;
      RelationalExp* rhs;
  };

  class ArrayAccess : public Expression {
    public:
      ArrayAccess(Var *lhs_, std::vector<Expression*> rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Var* lhs;
      std::vector<Expression*> rhs;
  };

  class ModelDeref : public Expression {
    public:
      ModelDeref(Var *var_) : var(var_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Var* var;
  };

  class RelationalArrayAccess : public RelationalExp {
    public:
      RelationalArrayAccess(relation_t relation_,
                            Var *lhs_,
                            std::vector<RelationalExp*> rhs_,
                            bool check_spec_ = true) :
          relation(relation_),
          lhs(lhs_),
          rhs(rhs_),
          check_spec(check_spec_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      relation_t relation;
      Var* lhs;
      std::vector<RelationalExp*> rhs;
      bool check_spec;
  };

  class SpecArrayAccess : public RelationalExp {
    public:
      SpecArrayAccess(Var *lhs_, std::vector<RelationalExp*> rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Var* lhs;
      std::vector<RelationalExp*> rhs;
  };

  class RelationalModelDeref : public RelationalExp {
    public:
      RelationalModelDeref(Var *var_) : var(var_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Var* var;
  };

  class BoolExp: public Expression {
    public:
      BoolExp() {}
      BoolExp(bool_t op_, Expression *lhs_, Expression *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      bool_t op;
      Expression* lhs;
      Expression* rhs;
  };

  class Forall : public BoolExp {
    public:
      Forall(Var* var_, BoolExp* exp_) :
          var(var_), exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* var;
      BoolExp* exp;
  };

  class PropertyApplication : public BoolExp {
    public:
      PropertyApplication(Var* name_, VarList* args_) :
        name(name_), args(args_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* name;
      VarList* args;
  };


  class RelationalBoolExp : public RelationalExp {
    public:
      RelationalBoolExp() {}
      RelationalBoolExp(bool_t op_, RelationalExp *lhs_, RelationalExp *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      bool_t op;
      RelationalExp* lhs;
      RelationalExp* rhs;
  };

  class RelationalPropertyApplication : public RelationalBoolExp {
    public:
      RelationalPropertyApplication(Var* name_, VarList* args_) :
        name(name_), args(args_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* name;
      VarList* args;
  };

  class SpecPropertyApplication : public RelationalBoolExp {
    public:
      SpecPropertyApplication(Var* name_, RelationalVarList* args_) :
        name(name_), args(args_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* name;
      RelationalVarList* args;
  };

  class RelationalNormal : public RelationalBoolExp {
    public:
      RelationalNormal(RelationalExp* exp_) : exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      RelationalExp* exp;
  };

  class RelationalForall : public RelationalBoolExp  {
    public:
      RelationalForall(Var* var_, RelationalBoolExp* exp_) :
          var(var_), exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* var;
      RelationalBoolExp* exp;
  };

  class RelationalExists : public RelationalBoolExp  {
    public:
      RelationalExists(Var* var_, RelationalBoolExp* exp_) :
          var(var_), exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* var;
      RelationalBoolExp* exp;
  };

  class Statement : public LangNode {
    public:
  };

  class Copy : public Statement {
    public:
      Copy(Var* src_, Var* dest_) : src(src_), dest(dest_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* src;
      Var* dest;
  };

  class Declare : public Statement {
    public:
      Declare(type_t type_, VarList *vars_, Var* region_)
        : type(type_), vars(vars_), region(region_), specvar(false) { }
      virtual z3pair accept(ASTVisitor &visitor)  override;

      type_t type;
      VarList* vars;
      Var* region;
      bool specvar;
  };

  class DeclareMat : public Statement {
    public:
      DeclareMat(type_t type_, VarList *vars_, Var* region_)
        : type(type_), vars(vars_), region(region_), specvar(false) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      type_t type;
      VarList* vars;
      Var* region;
      bool specvar;
  };

  class DeclareLMat : public Statement {
    public:
      DeclareLMat(type_t type_, Var *var_, std::vector<int> dimensions_)
        : type(type_), var(var_), dimensions(dimensions_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      type_t type;
      Var* var;
      std::vector<int> dimensions;
  };


  class Assign : public Statement {
    public:
      Assign(Expression *lhs_, Expression *rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Expression* lhs;
      Expression* rhs;
  };

  class ExprList : public Statement {
    public:
      ExprList(Expression* car_, ExprList* cdr_) :
          car(car_), cdr(cdr_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Expression* car;
      ExprList* cdr;
  };

  class ArrayAssign : public Statement {
    public:
      ArrayAssign(Expression *lhs_, ExprList *rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Expression* lhs;
      ExprList* rhs;
  };

  class StatementList : public Statement {
    public:
      StatementList(Statement *lhs_, Statement *rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Statement* lhs;
      Statement* rhs;
  };


  class While : public Statement {
    public:
      While(BoolExp *cond_,
            BoolExp* nonrel_inv_,
            RelationalBoolExp* inv_,
            Statement *body_,
            bool inf_) :
          cond(cond_),
          nonrel_inv(nonrel_inv_),
          inv(inv_),
          body(body_),
          seen(false),
          inf(inf_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      BoolExp* cond;
      BoolExp* nonrel_inv;
      RelationalBoolExp* inv;
      Statement* body;
      bool seen;
      std::vector<RelationalBoolExp*> houdini_invs;
      std::vector<BoolExp*> nonrel_houdini_invs;
      bool inf;
  };

  class Block : public Statement {
    public:
      Block(Statement *body_) : body(body_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Statement* body;
  };


  class If : public Statement {
    public:
      If (BoolExp *cond_, Statement *if_body_, Statement *else_body_) :
          cond(cond_), if_body(if_body_), else_body(else_body_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      BoolExp * cond;
      Statement* if_body;
      Statement* else_body;
  };

  class Skip : public Statement {
    public:
      Skip() {}
      virtual z3pair accept(ASTVisitor &visitor) override;
  };

  class Assert : public Statement {
    public:
      Assert(BoolExp* assertion_) : assertion(assertion_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      BoolExp* assertion;
  };

  class RelationalAssume : public Statement {
    public:
      RelationalAssume(RelationalBoolExp* assumption_) :
          assumption(assumption_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      RelationalBoolExp* assumption;
  };

  class RelationalAssert : public Statement {
    public:
      RelationalAssert(RelationalBoolExp* assertion_) :
          assertion(assertion_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      RelationalBoolExp* assertion;
  };

  class Fail : public Statement {
    public:
      Fail(BoolExp* clause_) : clause(clause_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      BoolExp* clause;
  };

  class FaultyWrite : public Statement {
    public:
      FaultyWrite(Expression* dest_, Expression* val_) :
          dest(dest_), val(val_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      Expression* dest;
      Expression* val;
  };

  class DeclareList : public Statement {
    public:
      DeclareList(Declare *car_, DeclareList* cdr_) :
          car(car_), mat_car(nullptr), cdr(cdr_) {}
      DeclareList(DeclareMat *mat_car_, DeclareList* cdr_) :
          car(nullptr), mat_car(mat_car_), cdr(cdr_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Declare* car;
      DeclareMat* mat_car;
      DeclareList* cdr;
  };

  class Function : public Statement {
    public:
      Function(BoolExp* requires_,
               RelationalBoolExp* r_requires_,
               bool returns_matrix_,
               type_t type_,
               Var* name_,
               DeclareList* decls_,
               Statement* body_) :
          requires(requires_),
          r_requires(r_requires_),
          returns_matrix(returns_matrix_),
          type(type_),
          name(name_),
          decls(decls_),
          body(body_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      BoolExp* requires;
      RelationalBoolExp* r_requires;
      bool returns_matrix;
      type_t type;
      Var* name;
      DeclareList* decls;
      Statement* body;
  };

  class Property : public Statement {
    public:
      Property(Var* name_, DeclareList* decls_, BoolExp* prop_) :
          name(name_), decls(decls_), prop(prop_) {}
      virtual z3pair accept(ASTVisitor& visitor) override;

      Var* name;
      DeclareList* decls;
      BoolExp* prop;
  };

  class RelationalProperty : public Statement {
    public:
      RelationalProperty(Var* name_,
                         DeclareList* decls_,
                         RelationalBoolExp* prop_) :
          name(name_), decls(decls_), prop(prop_) {}
      virtual z3pair accept(ASTVisitor& visitor) override;

      Var* name;
      DeclareList* decls;
      RelationalBoolExp* prop;
  };

  class Return : public Statement {
    public:
      Return(Expression* exp_) : exp(exp_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Expression* exp;
  };
}
