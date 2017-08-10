#include "ConjunctionBreaker.h"

#include "../common.h"

#define NONREL_NOTHING(type) \
  z3pair ConjunctionBreaker::visit(type& node) { \
    nonrel_invs.push_back(&node); \
    RETURN_VOID; \
  }

#define REL_NOTHING(type) \
  z3pair ConjunctionBreaker::visit(type& node) { \
    invs.push_back(&node); \
    RETURN_VOID; \
  }

namespace lang {
  ConjunctionBreaker::ConjunctionBreaker(RelationalBoolExp* inv) {
    invs.push_back(inv);
  }

  ConjunctionBreaker::ConjunctionBreaker(BoolExp* inv) {
    nonrel_invs.push_back(inv);
  }

  inv_vec ConjunctionBreaker::fissure() {
    assert(!invs.empty());
    if (invs.size() != 1) return invs;

    do {
      modified = false;
      inv_vec old_invs(invs);
      inv_vec new_invs;
      for (RelationalExp* inv : old_invs) {
        invs.clear();
        inv->accept(*this);
        new_invs.insert(new_invs.end(), invs.begin(), invs.end());

        assert(invs.size() == 1 || invs.size() == 2);
      }
      invs = new_invs;
      assert(invs.size() >= old_invs.size());
    } while (modified);

    return invs;
  }

  nonrel_inv_vec ConjunctionBreaker::nonrel_fissure() {
    assert(!nonrel_invs.empty());
    if (nonrel_invs.size() != 1) return nonrel_invs;

    do {
      modified = false;
      nonrel_inv_vec old_invs(nonrel_invs);
      nonrel_inv_vec new_invs;
      for (Expression* inv : old_invs) {
        nonrel_invs.clear();
        inv->accept(*this);
        new_invs.insert(new_invs.end(), nonrel_invs.begin(), nonrel_invs.end());

        assert(nonrel_invs.size() == 1 || nonrel_invs.size() == 2);
      }
      nonrel_invs = new_invs;
      assert(nonrel_invs.size() >= old_invs.size());
    } while (modified);

    return nonrel_invs;
  }


  z3pair ConjunctionBreaker::visit(RelationalBoolExp& node) {
    switch (node.op) {
      case AND:
        {
          modified = true;

          RelationalBoolExp* child = dynamic_cast<RelationalBoolExp*>(node.lhs);
          assert(child);
          invs.push_back(child);
          child = dynamic_cast<RelationalBoolExp*>(node.rhs);
          assert(child);
          invs.push_back(child);
        }
        break;
      case IMPLIES:
        {
          inv_vec new_invs(invs);
          invs.clear();
          node.rhs->accept(*this);

          for (RelationalExp* inv : invs) {
            new_invs.push_back(new RelationalBoolExp(IMPLIES, node.lhs, inv));
          }

          invs = new_invs;
        }
        break;
      case EQUALS:
      case NEQ:
      case LT:
      case XOR:
      case OR:
      case LTEQ:
        invs.push_back(&node);
    }

    RETURN_VOID;
  }

  z3pair ConjunctionBreaker::visit(BoolExp& node) {
    switch (node.op) {
      case AND:
        {
          modified = true;

          BoolExp* child = dynamic_cast<BoolExp*>(node.lhs);
          assert(child);
          nonrel_invs.push_back(child);
          child = dynamic_cast<BoolExp*>(node.rhs);
          assert(child);
          nonrel_invs.push_back(child);
        }
        break;
      case IMPLIES:
        {
          nonrel_inv_vec new_invs(nonrel_invs);
          nonrel_invs.clear();
          node.rhs->accept(*this);

          for (Expression* inv : nonrel_invs) {
            new_invs.push_back(new BoolExp(IMPLIES, node.lhs, inv));
          }

          nonrel_invs = new_invs;
        }
        break;
      case EQUALS:
      case NEQ:
      case LT:
      case XOR:
      case OR:
      case LTEQ:
        nonrel_invs.push_back(&node);
    }

    RETURN_VOID;
  }

  NONREL_NOTHING(Forall)
  REL_NOTHING(RelationalForall)
  REL_NOTHING(RelationalExists)
  NONREL_NOTHING(PropertyApplication)
  REL_NOTHING(RelationalPropertyApplication)
  REL_NOTHING(SpecPropertyApplication)
}
