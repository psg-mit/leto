#pragma once

#include <vector>

#include "LangNodes.h"
#include "ASTVisitor.h"

namespace lang {
  typedef std::vector<RelationalExp*> inv_vec;

  class ConjunctionBreaker : public ASTVisitor {
    public:
      ConjunctionBreaker(RelationalBoolExp* inv);

      /**
       * Breaks the RelationalBoolExp this object was created with into a
       * vector of individual invariants, then returns a *copy* of that vector.
       *
       * If this function was already called once, it will return the cached
       * vector generated from the first time it was called
       */
      inv_vec fissure();

      virtual z3pair visit(RelationalBoolExp &node) override;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
      virtual z3pair visit(Block &node) override {assert(false);}
      virtual z3pair visit(VarList &node) override {assert(false);}
      virtual z3pair visit(StatementList &node) override {assert(false);}
      virtual z3pair visit(Var &node) override {assert(false);}
      virtual z3pair visit(Assign &node) override {assert(false);}
      virtual z3pair visit(Declare &node) override {assert(false);}
      virtual z3pair visit(BoolExp &node) override {assert(false);}
      virtual z3pair visit(RelationalVar &node) override {assert(false);}
      virtual z3pair visit(SpecVar &node) override {assert(false);}
      virtual z3pair visit(BinOp &node) override {assert(false);}
      virtual z3pair visit(RelationalNormal &node) override {assert(false);}
      virtual z3pair visit(RelationalBinOp &node) override {assert(false);}
      virtual z3pair visit(RelationalInt &node) override {assert(false);}
      virtual z3pair visit(RelationalBool &node) override {assert(false);}
      virtual z3pair visit(Bool &node) override {assert(false);}
      virtual z3pair visit(Int &node) override {assert(false);}
      virtual z3pair visit(ArrayAccess &node) override {assert(false);}
      virtual z3pair visit(RelationalArrayAccess &node) override {assert(false);}
      virtual z3pair visit(SpecArrayAccess &node) override {assert(false);}
      virtual z3pair visit(If &node) override {assert(false);}
      virtual z3pair visit(While &node) override {assert(false);}
      virtual z3pair visit(Float &node) override {assert(false);}
      virtual z3pair visit(RelationalFloat &node) override {assert(false);}
      virtual z3pair visit(Real &node) override {assert(false);}
      virtual z3pair visit(RelationalReal &node) override {assert(false);}
      virtual z3pair visit(DeclareMat &node) override {assert(false);}
      virtual z3pair visit(DeclareLMat &node) override {assert(false);}
      virtual z3pair visit(ModelDeref &node) override {assert(false);}
      virtual z3pair visit(RelationalModelDeref &node) override {assert(false);}
      virtual z3pair visit(Skip &node) override {assert(false);}
      virtual z3pair visit(Assert &node) override {assert(false);}
      virtual z3pair visit(RelationalAssume &node) override {assert(false);}
      virtual z3pair visit(RelationalAssert &node) override {assert(false);}
      virtual z3pair visit(Fail &node) override {assert(false);}
      virtual z3pair visit(Copy &node) override {assert(false);}
      virtual z3pair visit(Exponent &node) override {assert(false);}
      virtual z3pair visit(ExprList &node) override {assert(false);}
      virtual z3pair visit(ArrayAssign &node) override {assert(false);}
      virtual z3pair visit(RelationalForall &node) override {assert(false);}
      virtual z3pair visit(FaultyRead &node) override {assert(false);}
      virtual z3pair visit(FaultyWrite &node) override {assert(false);}
#pragma clang diagnostic pop

    private:
      inv_vec invs;
      bool modified;

  };
}
