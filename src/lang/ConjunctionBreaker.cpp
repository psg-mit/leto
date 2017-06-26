#include "ConjunctionBreaker.h"

#include "../common.h"

namespace lang {
  ConjunctionBreaker::ConjunctionBreaker(RelationalBoolExp* inv) {
    invs.push_back(inv);
  }

  std::vector<RelationalExp*> ConjunctionBreaker::fissure() {
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
    if (node.op != AND) {
      invs.push_back(&node);
    } else {
      modified = true;
      invs.push_back(node.lhs);
      invs.push_back(node.rhs);
    }

    RETURN_VOID;
  }

}
