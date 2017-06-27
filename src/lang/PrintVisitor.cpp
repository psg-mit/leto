#include "ConjunctionBreaker.h"
#include "PrintVisitor.h"


namespace lang {
  void PrintVisitor::print_binop(operator_t op) {
    switch (op) {
      case OPLUS:
        if (compress) output += "+";
        else printf("+\n");
        break;
      case RPLUS:
        printf("+.\n");
        break;
      case OMINUS:
        if (compress) output += "-";
        else printf("-\n");
        break;
      case RMINUS:
        printf("-.\n");
        break;
      case OTIMES:
        if (compress) output += "*";
        else printf("*\n");
        break;
      case RTIMES:
        printf("*.\n");
        break;
      case ODIV:
        if (compress) output += "/";
        else printf("/\n");
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

  z3pair PrintVisitor::visit(Int &node) {
    printf("Int: %d\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Float &node) {
    printf("Float: %f\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(BinOp &node) {
    printf("BinOp: ");
    print_binop(node.op);
    node.lhs->accept(*this);
    node.rhs->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Block &node) {
    printf("Block:\n");
    node.body->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(While &node) {
    printf("While:\n");
    printf("  inf: %i\n", node.inf);
    printf("  Condition:\n");
    node.cond->accept(*this);
    printf("  Invariant:\n");
    node.inv->accept(*this);
    printf("  Body:\n");
    node.body->accept(*this);

    // Break invariant
    ConjunctionBreaker breaker(node.inv);
    inv_vec invs = breaker.fissure();

    printf("  Broken Invariant:\n");
    for (RelationalExp* e : invs) {
      printf("---BEGIN---\n");
      e->accept(*this);
      printf("---END---\n");
    }

    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(StatementList &node) {
    printf("StatementList:\n");
    printf("  lhs:\n");
    node.lhs->accept(*this);
    printf("  rhs:\n");
    node.rhs->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(ExprList &node) {
    printf("ExprList:\n");
    printf("  lhs:\n");
    node.car->accept(*this);
    if (node.cdr) {
      printf("  rhs:\n");
      node.cdr->accept(*this);
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Var &node) {
    if (compress) output += node.name;
    else printf("Var: %s\n", node.name.c_str());
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Assign &node) {
    printf("Assign:\n");
    printf("lhs:\n");
    node.lhs->accept(*this);
    printf("rhs:\n");
    node.rhs->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(ArrayAssign &node) {
    printf("ArrayAssign:\n");
    printf("lhs:\n");
    node.lhs->accept(*this);
    printf("rhs:\n");
    node.rhs->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(ArrayAccess &node) {
    printf("ArrayAccess:\n");
    printf("lhs:\n");
    node.lhs->accept(*this);
    printf("rhs:\n");
    for (Expression* exp : node.rhs) {
      exp->accept(*this);
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(SpecArrayAccess &node) {
    printf("SpecArrayAccess:\n");
    printf("lhs:\n");
    node.lhs->accept(*this);
    printf("rhs:\n");
    for (RelationalExp* exp : node.rhs) {
      exp->accept(*this);
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(If &node) {
    printf("If:\n");
    printf("  Condition:\n");
    node.cond->accept(*this);
    printf("  If Body:\n");
    node.if_body->accept(*this);
    printf("  Else Body:\n");
    node.else_body->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Declare &node) {
    printf("Declare:\n");
    printf("Type: ");
    switch (node.type) {
      case BOOL:
        printf("bool\n");
        break;
      case INT:
        printf("int\n");
        break;
      case REAL:
        printf("real\n");
        break;
      case FLOAT:
        printf("float\n");
        break;
    }
    printf("specvar: %d\n", node.specvar);
    node.vars->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(DeclareMat &node) {
    printf("DeclareMat:\n");
    printf("Type: ");
    switch (node.type) {
      case BOOL:
        printf("bool\n");
        break;
      case INT:
        printf("int\n");
        break;
      case REAL:
        printf("real\n");
        break;
      case FLOAT:
        printf("float\n");
        break;
    }

    printf("specvar: %d\n", node.specvar);

    node.vars->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(DeclareLMat &node) {
    printf("DeclareLMat:\n");
    printf("Type: ");
    switch (node.type) {
      case BOOL:
        printf("bool\n");
        break;
      case INT:
        printf("int\n");
        break;
      case REAL:
        printf("real\n");
        break;
      case FLOAT:
        printf("float\n");
        break;
    }

    printf("Dimension: %d", node.dimensions.at(0));
    for (size_t i = 1; i < node.dimensions.size(); ++i) {
      printf(" x %d", node.dimensions.at(i));
    }
    printf("\n");

    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(BoolExp &node) {
    printf("BoolExp: ");
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
      case NEQ:
        printf("!=\n");
        break;
      case AND:
        printf("&&\n");
        break;
      case IMPLIES:
        printf("->\n");
        break;
      case OR:
        printf("||\n");
        break;
    }

    node.lhs->accept(*this);
    node.rhs->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(ModelDeref &node) {
    printf("ModelDeref:\n");
    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalVar &node) {
    if (!compress) printf("RelationalVar:\n");
    node.var->accept(*this);
    if (!compress) printf("Relation: ");
    switch (node.relation) {
      case ORIGINAL:
        if (compress) output += "<o>";
        else printf("original\n");
        break;
      case RELAXED:
        if (compress) output += "<r>";
        else printf("relaxed\n");
        break;
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(SpecVar &node) {
    if (!compress) printf("SpecVar:\n");
    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalBoolExp &node) {
    if (compress) output += "(";
    else printf("RelationalBoolExp: ");
    switch (node.op) {
      case XOR:
        if (compress) output += "^";
        else printf("^\n");
        break;
      case EQUALS:
        if (compress) output += "==";
        else printf("==\n");
        break;
      case LT:
        if (compress) output += "<";
        else printf("<\n");
        break;
      case LTEQ:
        if (compress) output += "<=";
        else printf("<=\n");
        break;
      case NEQ:
        if (compress) output += "!=";
        else printf("!=\n");
        break;
      case AND:
        if (compress) output += "&&";
        else printf("&&\n");
        break;
      case IMPLIES:
        if (compress) output += "->";
        else printf("->\n");
        break;
      case OR:
        if (compress) output += "||";
        else printf("||\n");
        break;
    }

    if (compress) output += " ";
    node.lhs->accept(*this);
    if (compress) output += " ";
    node.rhs->accept(*this);
    if (compress) output += ")";
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalBinOp &node) {
    if (compress) output += "(";
    else printf("RelationalBinOp: ");
    print_binop(node.op);
    if (compress) output += " ";
    node.lhs->accept(*this);
    if (compress) output += " ";
    node.rhs->accept(*this);
    if (compress) output += ")";
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalInt &node) {
    if (compress) output += std::to_string(node.value);
    else printf("RelationalInt: %d\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalBool &node) {
    if (compress) output += std::to_string(node.value);
    else printf("RelationalBool: %d\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Bool &node) {
    printf("Bool: %d\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalFloat &node) {
    if (compress) output += std::to_string(node.value);
    else printf("RelationalFloat: %f\n", node.value);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalArrayAccess &node) {
    if (!compress) {
      printf("RelationalArrayAccess:\n");

      printf("lhs:\n");
    }
    node.lhs->accept(*this);

    if (!compress) printf("Relation: ");
    switch (node.relation) {
      case ORIGINAL:
        if (compress) output += "<o>";
        else printf("original\n");
        break;
      case RELAXED:
        if (compress) output += "<r>";
        else printf("relaxed\n");
        break;
    }

    if (!compress) printf("rhs:\n");
    for (Expression* exp : node.rhs) {
      if (compress) output += "[";
      exp->accept(*this);
      if (compress) output += "]";
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Real &node) {
    printf("Real:\n");
    printf("  numerator: %d\n", node.numerator);
    printf("  denominator : %d\n", node.denominator);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalReal &node) {
    if (compress) {
      output += "real(" +
                std::to_string(node.numerator) +
                ", " +
                std::to_string(node.denominator) +
                ")";
    } else {
      printf("RelationalReal:\n");
      printf("  numerator: %d\n", node.numerator);
      printf("  denominator : %d\n", node.denominator);
    }
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalModelDeref &node) {
    if (compress) output += "model.";
    else printf("RelationalModelDeref:\n");
    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalNormal &node) {
    if (compress) output += "normal(";
    else printf("RelationalNormal:\n");
    node.exp->accept(*this);
    if (compress) output += (")");
    return {nullptr, nullptr};
  }

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
  z3pair PrintVisitor::visit(Skip &node) {
    printf("Skip\n");
    return {nullptr, nullptr};
  }
#pragma clang diagnostic pop

  z3pair PrintVisitor::visit(Assert &node) {
    printf("Assert:\n");
    node.assertion->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalAssume &node) {
    printf("RelationalAssume:\n");
    node.assumption->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalAssert &node) {
    printf("RelationalAssert:\n");
    node.assertion->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Fail &node) {
    printf("Fail:\n");
    node.clause->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Copy &node) {
    printf("Copy:\n");
    printf("  src:\n");
    node.src->accept(*this);
    printf("  dest:\n");
    node.dest->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Exponent &node) {
    printf("Exponent:\n");
    printf("  base:\n");
    node.base->accept(*this);
    printf("  exp:\n");
    node.exp->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalForall &node) {
    if (compress) {
      output += "forall(";
    } else {
      printf("RelationalForall:\n");
      printf("  var:\n");
    }
    node.var->accept(*this);
    if (compress) output += ")(";
    else printf("  exp:\n");
    node.exp->accept(*this);
    if (compress) output += (")");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Forall &node) {
    if (compress) {
      output += "forall(";
    } else {
      printf("RelationalForall:\n");
      printf("  var:\n");
    }
    node.var->accept(*this);
    if (compress) output += ")(";
    else printf("  exp:\n");
    node.exp->accept(*this);
    if (compress) output += (")");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(FaultyRead &node) {
    printf("FaultyRead:\n");
    printf("  var:\n");
    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(FaultyWrite &node) {
    printf("FaultyRead:\n");
    printf("  dest:\n");
    node.dest->accept(*this);
    printf("  val:\n");
    node.val->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(VarList &node) {
    printf("VarList: ");
    if (node.car) {
      printf("\n");
      node.car->accept(*this);

      if (!node.dimensions.empty()) {
        printf("Dimensions:\n");
        for (Expression* exp : node.dimensions) {
          exp->accept(*this);
        }
      }
      if (node.cdr) node.cdr->accept(*this);
    }
    else printf("nil\n");

    return {nullptr, nullptr};
  }
}
