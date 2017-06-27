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
              std::vector<RelationalExp*> dimensions_,
              VarList *cdr_) : car(car_), dimensions(dimensions_), cdr(cdr_) {}
      virtual z3pair accept(ASTVisitor &visitor) override;

      Var* car;
      std::vector<RelationalExp*> dimensions;
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
      BoolExp(bool_t op_, Expression *lhs_, Expression *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      bool_t op;
      Expression* lhs;
      Expression* rhs;
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
      Declare(type_t type_, VarList *vars_)
        : type(type_), vars(vars_), specvar(false) { }
      virtual z3pair accept(ASTVisitor &visitor)  override;

      type_t type;
      VarList* vars;
      bool specvar;
  };

  class DeclareMat : public Statement {
    public:
      DeclareMat(type_t type_, VarList *vars_)
        : type(type_), vars(vars_), specvar(false) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      type_t type;
      VarList* vars;
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
            RelationalBoolExp* inv_,
            Statement *body_,
            bool inf_) :
          cond(cond_), inv(inv_), body(body_), seen(false), inf(inf_) {}
      virtual z3pair accept(ASTVisitor &visitor)  override;

      BoolExp* cond;
      RelationalBoolExp* inv;
      Statement* body;
      bool seen;
      std::vector<RelationalBoolExp*> houdini_invs;
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

}
