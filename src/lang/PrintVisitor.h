#pragma once

#include "LangNodes.h"
#include "ASTVisitor.h"

namespace lang {
  class PrintVisitor : public ASTVisitor {
    public:
      PrintVisitor() {}
      virtual z3pair visit(Int &node) override;
      virtual z3pair visit(BinOp &node) override;
      virtual z3pair visit(Block &node) override;
      virtual z3pair visit(While &node) override;
      virtual z3pair visit(StatementList &node) override;
      virtual z3pair visit(Var &node) override;
      virtual z3pair visit(Assign &node) override;
      virtual z3pair visit(ArrayAccess &node) override;
      virtual z3pair visit(If &node) override;
      virtual z3pair visit(Declare &node) override;
      virtual z3pair visit(BoolExp &node) override;
      virtual z3pair visit(RelationalVar &node) override;
      virtual z3pair visit(SpecVar &node) override;
      virtual z3pair visit(RelationalBoolExp &node) override;
      virtual z3pair visit(RelationalBinOp &node) override;
      virtual z3pair visit(RelationalInt &node) override;
      virtual z3pair visit(RelationalArrayAccess &node) override;
      virtual z3pair visit(SpecArrayAccess &node) override;
      virtual z3pair visit(Float &node) override;
      virtual z3pair visit(RelationalFloat &node) override;
      virtual z3pair visit(DeclareMat &node) override;
      virtual z3pair visit(DeclareLMat &node) override;
      virtual z3pair visit(ModelDeref &node) override;
      virtual z3pair visit(RelationalBool &node) override;
      virtual z3pair visit(Bool &node) override;
      virtual z3pair visit(Real &node) override;
      virtual z3pair visit(RelationalReal &node) override;
      virtual z3pair visit(RelationalModelDeref &node) override;
      virtual z3pair visit(RelationalNormal &node) override;
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
  };
}
