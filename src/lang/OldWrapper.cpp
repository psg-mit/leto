#include <cassert>

#include "OldWrapper.h"

#define WRAP_NONE(type) \
  z3pair OldWrapper::visit(type& node) { \
    nodes.push_back(&node); \
    RETURN_VOID; \
  }

namespace lang {
  OldWrapper::OldWrapper(RelationalBoolExp* inv, Var* label_) {

    modified = false;
    label = label_;

    inv->accept(*this);
    assert(nodes.size() == 1);

    if (modified) {
      wrapped = dynamic_cast<RelationalBoolExp*>(nodes.back());
      assert(wrapped);
    } else {
      wrapped = nullptr;
    }
  }

  z3pair OldWrapper::visit(RelationalBoolExp& node) {
    node.lhs->accept(*this);
    RelationalExp* lexp = nodes.back();
    nodes.pop_back();

    node.rhs->accept(*this);
    RelationalExp* rexp = nodes.back();
    nodes.pop_back();


    if  (modified) {
      RelationalBoolExp* wrap = new RelationalBoolExp(node.op, lexp, rexp);
      nodes.push_back(wrap);
    } else {
      nodes.push_back(&node);
    }

    RETURN_VOID;
  }


  z3pair OldWrapper::visit(RelationalModelDeref &node) {
    modified = true;
    SpecArrayAccess* wrap = new SpecArrayAccess(label, {&node});
    nodes.push_back(wrap);
    RETURN_VOID;
  }


  WRAP_NONE(RelationalPropertyApplication)
  WRAP_NONE(SpecPropertyApplication)
  WRAP_NONE(RelationalForall)
  WRAP_NONE(RelationalExists)
  WRAP_NONE(RelationalVar)
  WRAP_NONE(RelationalBinOp)
  WRAP_NONE(RelationalInt)
  WRAP_NONE(RelationalBool)
  WRAP_NONE(RelationalArrayAccess)
  WRAP_NONE(RelationalReal)
  WRAP_NONE(SpecArrayAccess)
  WRAP_NONE(SpecVar)
}
