#include "ConjunctionBreaker.h"

#include "../common.h"

namespace lang {
  ConjunctionBreaker::ConjunctionBreaker(RelationalBoolExp* inv) {
    invs.push_back(inv);
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

  z3pair ConjunctionBreaker::visit(RelationalForall& node) {
    invs.push_back(&node);

    RETURN_VOID;
  }

}
