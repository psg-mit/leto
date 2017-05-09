#pragma once
#include <string>

#include <z3++.h>

#include "../common.h"

namespace model {
  enum bool_t {AND, EQUALS, LT, XOR, LTEQ};

  class ASTVisitor;

  class ModelNode {
    public:
      virtual z3::expr* accept(ASTVisitor &visitor) const = 0;
      virtual ~ModelNode() {}
  };

  class Expression : public ModelNode { };

  class Statement : public ModelNode { };

  class BoolExp : public Expression { };

  class Int : public Expression {
    public:
      Int(int value_) : value(value_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const int value;
  };

  class Float : public Expression {
    public:
      Float(float value_) : value(value_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const float value;
  };

  class Bool : public BoolExp {
    public:
      Bool(bool value_) : value(value_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const bool value;
  };

  class BinOp : public Expression {
    public:
      BinOp(operator_t op_, const Expression *lhs_, const Expression *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const operator_t op;
      const Expression* const lhs;
      const Expression* const rhs;
  };

  class Var : public Expression {
    public:
      Var(const std::string &name_) : name(name_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const std::string name;
  };

  class Declare : public Statement {
    public:
      Declare(type_t type_, const Var *var_) : type(type_), var(var_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const type_t type;
      const Var* const var;
  };

  class StatementList : public Statement {
    public:
      StatementList(const Statement *lhs_, const Statement *rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const Statement* const lhs;
      const Statement* const rhs;
  };

  class Assign : public Statement {
    public:
      Assign(const Expression *lhs_, const Expression *rhs_) :
          lhs(lhs_), rhs(rhs_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const Expression* const lhs;
      const Expression* const rhs;
  };

  class BoolBinOp: public BoolExp {
    public:
      BoolBinOp(bool_t op_, const Expression *lhs_, const Expression *rhs_) :
          op(op_), lhs(lhs_), rhs(rhs_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const bool_t op;
      const Expression* const lhs;
      const Expression* const rhs;
  };

  class VarList : public Statement {
    public:
      VarList(const Var *car_, const VarList *cdr_) : car(car_), cdr(cdr_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const Var* const car;
      const VarList* const cdr;
  };

  class Operator : public Statement {
    public:
      Operator(operator_t op_,
               const Var *arg1_,
               const Var *arg2_,
               const BoolExp *when_,
               const VarList* modifies_,
               const BoolExp *ensures_) :
          op(op_),
          arg1(arg1_),
          arg2(arg2_),
          when(when_),
          modifies(modifies_),
          ensures(ensures_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const operator_t op;
      const Var* const arg1;
      const Var* const arg2;
      const BoolExp* const when;
      const VarList* const  modifies;
      const BoolExp* const ensures;
  };

  class Block : public Statement {
    public:
      Block(const Statement *body_) : body(body_) {}
      virtual z3::expr* accept(ASTVisitor &visitor) const override;

      const Statement* const body;
  };
}
