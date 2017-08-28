#include "ModelNodes.h"
#include "ASTVisitor.h"

namespace model {
  z3::expr* Int::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Float::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* BinOp::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Var::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Bool::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Declare::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* StatementList::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Assign::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* BoolBinOp::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Operator::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Block::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* VarList::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Old::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }

  z3::expr* Real::accept(ASTVisitor &visitor) const {
    return visitor.visit(*this);
  }
}
