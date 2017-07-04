#include "LangNodes.h"
#include "ASTVisitor.h"

namespace lang {
  z3pair Int::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalBool::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Bool::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair BinOp::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair While::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Block::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair StatementList::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Var::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Assign::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair ArrayAccess::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair If::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Declare::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair DeclareMat::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair DeclareLMat::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair BoolExp::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalVar::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair SpecVar::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalBoolExp::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalBinOp::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalInt::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalArrayAccess::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair SpecArrayAccess::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Float::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalFloat::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair ModelDeref::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalModelDeref::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalNormal::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Real::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalReal::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Skip::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Assert::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalAssume::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalAssert::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Fail::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Copy::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Exponent::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair ExprList::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair ArrayAssign::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair RelationalForall::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair Forall::accept(ASTVisitor &visitor)  {
    return visitor.visit(*this);
  }

  z3pair FaultyRead::accept(ASTVisitor &visitor) {
    return visitor.visit(*this);
  }

  z3pair FaultyWrite::accept(ASTVisitor &visitor) {
    return visitor.visit(*this);
  }

  z3pair VarList::accept(ASTVisitor &visitor) {
    return visitor.visit(*this);
  }

  z3pair DeclareList::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair Function::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair Return::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair Property::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair RelationalProperty::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair PropertyApplication::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }

  z3pair RelationalPropertyApplication::accept(ASTVisitor& visitor) {
    return visitor.visit(*this);
  }
}
