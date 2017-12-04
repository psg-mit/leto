#pragma once

#include "LangNodes.h"

namespace lang {
  class ASTVisitor {
    public:
      virtual z3pair visit(Int &node) = 0;
      virtual z3pair visit(BinOp &node) = 0;
      virtual z3pair visit(Block &node) = 0;
      virtual z3pair visit(While &node) = 0;
      virtual z3pair visit(StatementList &node) = 0;
      virtual z3pair visit(Var &node) = 0;
      virtual z3pair visit(Assign &node) = 0;
      virtual z3pair visit(ArrayAccess &node) = 0;
      virtual z3pair visit(If &node) = 0;
      virtual z3pair visit(Declare &node) = 0;
      virtual z3pair visit(BoolExp &node) = 0;
      virtual z3pair visit(RelationalVar &node) = 0;
      virtual z3pair visit(RelationalVarList &node) = 0;
      virtual z3pair visit(SpecVar &node) = 0;
      virtual z3pair visit(RelationalBoolExp &node) = 0;
      virtual z3pair visit(RelationalBinOp &node) = 0;
      virtual z3pair visit(RelationalInt &node) = 0;
      virtual z3pair visit(RelationalArrayAccess &node) = 0;
      virtual z3pair visit(SpecArrayAccess &node) = 0;
      virtual z3pair visit(Float &node) = 0;
      virtual z3pair visit(RelationalFloat &node) = 0;
      virtual z3pair visit(Real &node) = 0;
      virtual z3pair visit(RelationalReal &node) = 0;
      virtual z3pair visit(DeclareMat &node) = 0;
      virtual z3pair visit(DeclareLMat &node) = 0;
      virtual z3pair visit(ModelDeref &node) = 0;
      virtual z3pair visit(RelationalModelDeref &node) = 0;
      virtual z3pair visit(RelationalBool &node) = 0;
      virtual z3pair visit(Bool &node) = 0;
      virtual z3pair visit(RelationalNormal &node) = 0;
      virtual z3pair visit(Skip &node) = 0;
      virtual z3pair visit(Assert &node) = 0;
      virtual z3pair visit(RelationalAssume &node) = 0;
      virtual z3pair visit(RelationalAssert &node) = 0;
      virtual z3pair visit(Fail &node) = 0;
      virtual z3pair visit(Copy &node) = 0;
      virtual z3pair visit(Exponent &node) = 0;
      virtual z3pair visit(ExprList &node) = 0;
      virtual z3pair visit(ArrayAssign &node) = 0;
      virtual z3pair visit(RelationalForall &node) = 0;
      virtual z3pair visit(RelationalExists &node) = 0;
      virtual z3pair visit(Forall &node) = 0;
      virtual z3pair visit(FaultyRead &node) = 0;
      virtual z3pair visit(FaultyWrite &node) = 0;
      virtual z3pair visit(VarList &node) = 0;
      virtual z3pair visit(DeclareList &node) = 0;
      virtual z3pair visit(Function &node) = 0;
      virtual z3pair visit(Return &node) = 0;
      virtual z3pair visit(Property &node) = 0;
      virtual z3pair visit(RelationalProperty &node) = 0;
      virtual z3pair visit(PropertyApplication &node) = 0;
      virtual z3pair visit(RelationalPropertyApplication &node) = 0;
      virtual z3pair visit(SpecPropertyApplication &node) = 0;
      virtual z3pair visit(Try &node) = 0;
      virtual z3pair visit(Commit &node) = 0;

      virtual ~ASTVisitor() {}
  };
}
