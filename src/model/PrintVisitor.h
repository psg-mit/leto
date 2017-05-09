#pragma once

#include "ModelNodes.h"
#include "ASTVisitor.h"

namespace model {
  class PrintVisitor : public ASTVisitor {
    public:
      PrintVisitor() {}
      virtual z3::expr* visit(const Int &node) override;
      virtual z3::expr* visit(const Float &node) override;
      virtual z3::expr* visit(const BinOp &node) override;
      virtual z3::expr* visit(const Var &node) override;
      virtual z3::expr* visit(const Bool &node) override;
      virtual z3::expr* visit(const Declare &node) override;
      virtual z3::expr* visit(const StatementList &node) override;
      virtual z3::expr* visit(const Assign &node) override;
      virtual z3::expr* visit(const BoolBinOp &node) override;
      virtual z3::expr* visit(const Operator &node) override;
      virtual z3::expr* visit(const Block &node) override;
      virtual z3::expr* visit(const VarList &node) override;
  };
}
