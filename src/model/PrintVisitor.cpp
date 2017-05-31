#include <cstdio>

#include "PrintVisitor.h"

namespace model {
  static void print_binop(operator_t op) {
    switch (op) {
      case OPLUS:
        printf("+\n");
        break;
      case RPLUS:
        printf("+.\n");
        break;
      case OMINUS:
        printf("-\n");
        break;
      case RMINUS:
        printf("-.\n");
        break;
      case OTIMES:
        printf("*\n");
        break;
      case RTIMES:
        printf("*.\n");
        break;
      case ODIV:
        printf("/\n");
        break;
      case RDIV:
        printf("/.\n");
        break;
      case FREAD:
        printf("fread\n");
        break;
      case FWRITE:
        printf("fwrite\n");
        break;
    }
  }

  z3::expr* PrintVisitor::visit(const Int &node) {
    printf("Int: %d\n", node.value);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Float &node) {
    printf("Float: %f\n", node.value);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const BinOp &node) {
    printf("BinOp: ");
    print_binop(node.op);
    node.lhs->accept(*this);
    node.rhs->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Var &node) {
    printf("Var: %s\n", node.name.c_str());
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Bool &node) {
    printf("Bool: %s\n", node.value ? "true" : "false");
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Declare &node) {
    printf("Declare:\n");
    printf("Type: ");
    switch (node.type) {
      case BOOL:
        printf("bool\n");
        break;
      case INT:
        printf("int\n");
        break;
      case FLOAT:
        printf("float\n");
        break;
      case REAL:
        printf("real\n");
        break;
    }
    node.var->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const StatementList &node) {
    printf("StatementList:\n");
    printf("  lhs:\n");
    node.lhs->accept(*this);
    printf("  rhs:\n");
    node.rhs->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Assign &node) {
    printf("Assign:\n");
    printf("lhs:\n");
    node.lhs->accept(*this);
    printf("rhs:\n");
    node.rhs->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const BoolBinOp &node) {
    printf("BoolBinOp: ");
    switch (node.op) {
      case XOR:
        printf("^\n");
        break;
      case EQUALS:
        printf("==\n");
        break;
      case LT:
        printf("<\n");
        break;
      case LTEQ:
        printf("<=\n");
        break;
      case AND:
        printf("&&\n");
        break;
      case OR:
        printf("||\n");
        break;
    }

    node.lhs->accept(*this);
    node.rhs->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Operator &node) {
    printf("Operator: ");
    print_binop(node.op);
    printf("arg1:\n");
    node.arg1->accept(*this);
    if (node.op != FREAD) {
      printf("arg2:\n");
      node.arg2->accept(*this);
    }
    printf("when:\n");
    node.when->accept(*this);
    printf("modifies:\n");
    if (node.modifies) node.modifies->accept(*this);
    printf("ensures:\n");
    node.ensures->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const Block &node) {
    printf("Block:\n");
    node.body->accept(*this);
    return nullptr;
  }

  z3::expr* PrintVisitor::visit(const VarList &node) {
    printf("VarList: ");
    if (node.car) {
      printf("\n");
      node.car->accept(*this);
      if (node.cdr) node.cdr->accept(*this);
    }
    else printf("nil\n");
    return nullptr;
  }
}
