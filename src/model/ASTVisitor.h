#pragma once

#include <z3++.h>

#include "ModelNodes.h"

#define ARG1_STR "x1"
#define ARG2_STR "x2"
#define RESULT_STR "result"

namespace model {
  class ASTVisitor {
    public:
      virtual z3::expr* visit(const Int &node) = 0;
      virtual z3::expr* visit(const Float &node) = 0;
      virtual z3::expr* visit(const BinOp &node) = 0;
      virtual z3::expr* visit(const Var &node) = 0;
      virtual z3::expr* visit(const Bool &node) = 0;
      virtual z3::expr* visit(const Declare &node) = 0;
      virtual z3::expr* visit(const StatementList &node) = 0;
      virtual z3::expr* visit(const Assign &node) = 0;
      virtual z3::expr* visit(const BoolBinOp &node) = 0;
      virtual z3::expr* visit(const Operator &node) = 0;
      virtual z3::expr* visit(const Block &node) = 0;
      virtual z3::expr* visit(const VarList &node) = 0;
      virtual z3::expr* visit(const Old &node) = 0;
      virtual z3::expr* visit(const Real &node) = 0;
      virtual z3::expr* visit(const Commit &node) = 0;
      virtual z3::expr* visit(const Step &node) = 0;

      virtual ~ASTVisitor() {}
  };
}
