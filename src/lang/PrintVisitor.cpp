#include "ConjunctionBreaker.h"
#include "PrintVisitor.h"

static void print_type(type_t type) {
  switch (type) {
    case BOOL:
      printf("bool\n");
      break;
    case INT:
      printf("int\n");
      break;
    case UINT:
      printf("uint\n");
      break;
    case REAL:
      printf("real\n");
      break;
    case FLOAT:
      printf("float\n");
      break;
  }
}

namespace lang {
  template<typename T>
  void PrintVisitor::print_binop(T& node, std::string type) {
    if (compress) output += "(";
    else printf("%s: ", type.c_str());
    switch (node.op) {
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
    if (compress) output += " ";
    node.lhs->accept(*this);
    if (compress) output += " ";
    node.rhs->accept(*this);
    if (compress) output += ")";
  }

  template<typename T> void PrintVisitor::print_value(T& node) {
    if (compress) output += std::to_string(node.value);
    else std::cout << node.value << std::endl;
  }

  z3pair PrintVisitor::visit(Int &node) {
    print_value(node);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Float &node) {
    print_value(node);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(BinOp &node) {
    print_binop(node, "BinOp");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Block &node) {
    printf("Block:\n");
    node.body->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(While &node) {
    printf("While:\n");
    printf("  label:\n");
    node.label->accept(*this);
    printf("  inf: %i\n", node.inf);
    printf("  Condition:\n");
    node.cond->accept(*this);
    printf("  Non-Relational Invariant:\n");
    node.nonrel_inv->accept(*this);
    printf("  Relational Invariant:\n");
    node.inv->accept(*this);
    printf("  Body:\n");
    node.body->accept(*this);

    // Break invariant
    {
      ConjunctionBreaker breaker(node.nonrel_inv);
      nonrel_inv_vec invs = breaker.nonrel_fissure();

      printf("  Broken Nonrelational Invariant:\n");
      for (Expression* e : invs) {
        printf("---BEGIN---\n");
        e->accept(*this);
        printf("---END---\n");
      }
    }

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

  template<typename T> void PrintVisitor::print_array_access(T& node) {
    if (!compress) printf("lhs:\n");

    node.lhs->accept(*this);

    if (!compress) printf("rhs:\n");
    for (Expression* exp : node.rhs) {
      if (compress) output += "[";
      exp->accept(*this);
      if (compress) output += "]";
    }
  }

  z3pair PrintVisitor::visit(ArrayAccess &node) {
    if (!compress) printf("ArrayAccess:\n");
    print_array_access(node);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(SpecArrayAccess &node) {
    if (!compress) printf("SpecArrayAccess:\n");
    print_array_access(node);
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
    print_type(node.type);
    printf("specvar: %d\n", node.specvar);
    node.vars->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(DeclareMat &node) {
    printf("DeclareMat:\n");
    printf("Type: ");
    print_type(node.type);

    printf("specvar: %d\n", node.specvar);

    node.vars->accept(*this);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(DeclareLMat &node) {
    printf("DeclareLMat:\n");
    printf("Type: ");
    print_type(node.type);

    printf("Dimension: %d", node.dimensions.at(0));
    for (size_t i = 1; i < node.dimensions.size(); ++i) {
      printf(" x %d", node.dimensions.at(i));
    }
    printf("\n");

    node.var->accept(*this);
    return {nullptr, nullptr};
  }

  template<typename T>
  void PrintVisitor::print_bool_exp(T& node, std::string type) {
    if (compress) output += "(";
    else printf("%s: ", type.c_str());
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
  }

  z3pair PrintVisitor::visit(BoolExp &node) {
    print_bool_exp(node, "BoolExp");
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
    print_bool_exp(node, "RelationalBoolExp");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalBinOp &node) {
    print_binop(node, "RelationalBinOp");
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
    print_value(node);
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalFloat &node) {
    print_value(node);
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

  template<typename T>
  void PrintVisitor::print_real(T& node, std::string type) {
    if (compress) {
      output += "real(" +
                std::to_string(node.numerator) +
                ", " +
                std::to_string(node.denominator) +
                ")";
    } else {
      printf("%s:\n", type.c_str());
      printf("  numerator: %d\n", node.numerator);
      printf("  denominator : %d\n", node.denominator);
    }
  }

  z3pair PrintVisitor::visit(Real &node) {
    print_real(node, "Real");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalReal &node) {
    print_real(node, "RelationalReal");
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

  template<typename T>
  void PrintVisitor::print_forall(T& node, std::string type) {
    if (compress) {
      output += "forall(";
    } else {
      printf("%s:\n", type.c_str());
      printf("  var:\n");
    }
    node.var->accept(*this);
    if (compress) output += ")(";
    else printf("  exp:\n");
    node.exp->accept(*this);
    if (compress) output += (")");
  }

  z3pair PrintVisitor::visit(RelationalForall &node) {
    print_forall(node, "RelationalForall");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Forall &node) {
    print_forall(node, "Forall");
    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalExists &node) {
    if (compress) {
      output += "exists(";
    } else {
      printf("RelationalExists:\n");
      printf("  var:\n");
    }
    node.var->accept(*this);
    if (compress) output += ")(";
    else printf("  exp:\n");
    node.exp->accept(*this);
    if (compress) output += (")");

    RETURN_VOID;
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
    if (!compress) printf("VarList: ");
    if (node.car) {
      if (!compress) printf("\n");
      node.car->accept(*this);

      if (!compress && !node.dimensions.empty()) {
        printf("Dimensions:\n");
        for (Expression* exp : node.dimensions) {
          exp->accept(*this);
        }
      }
      if (node.cdr) {
        if (compress) output += ", ";
        node.cdr->accept(*this);
      }
    }
    else printf("nil\n");

    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(RelationalVarList &node) {
    if (!compress) printf("RelationalVarList: ");
    if (node.car) {
      if (!compress) printf("\n");
      node.car->accept(*this);

      if (node.cdr) {
        if (compress) output += ", ";
        node.cdr->accept(*this);
      }
    }
    else printf("nil\n");

    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(DeclareList &node) {
    printf("DeclareList: ");
    if (node.car) {
      printf("\n");
      node.car->accept(*this);

      if (node.cdr) node.cdr->accept(*this);
    } else if (node.mat_car) {
      printf("\n");
      node.mat_car->accept(*this);

      if (node.cdr) node.cdr->accept(*this);
    }
    else printf("nil\n");

    return {nullptr, nullptr};
  }

  z3pair PrintVisitor::visit(Function &node) {
    printf("Function:\n");
    printf("  requires:\n");
    node.requires->accept(*this);
    printf("  r_requires:\n");
    node.r_requires->accept(*this);
    printf("  returns_matrix: %d\n", node.returns_matrix);
    printf("  type:");
    print_type(node.type);
    printf("  name:\n");
    node.name->accept(*this);
    printf("  decls:\n");
    node.decls->accept(*this);
    printf("  body:\n");
    node.body->accept(*this);

    RETURN_VOID;
  }

  z3pair PrintVisitor::visit(Return &node) {
    printf("Return:\n");
    node.exp->accept(*this);

    RETURN_VOID;
  }

  template<typename T>
  void PrintVisitor::print_property(T& node, std::string type) {
    printf("%s:\n", type.c_str());
    printf("  name:\n");
    node.name->accept(*this);
    printf("  decls:\n");
    node.decls->accept(*this);
    printf("  prop:\n");
    node.prop->accept(*this);

  }

  z3pair PrintVisitor::visit(Property& node) {
    print_property(node, "Property");
    RETURN_VOID;
  }

  z3pair PrintVisitor::visit(RelationalProperty& node) {
    print_property(node, "RelationalProperty");
    RETURN_VOID;
  }

  template<typename T>
  void PrintVisitor::print_property_application(T& node, std::string type) {
    if (!compress) {
      printf("%s:\n", type.c_str());
      printf("  name:\n");
    }
    node.name->accept(*this);
    if (compress) output += "(";
    else printf("  args:\n");
    node.args->accept(*this);
    if (compress) output += ")";
  }

  z3pair PrintVisitor::visit(PropertyApplication& node) {
    print_property_application(node, "PropertyApplication");
    RETURN_VOID;
  }

  z3pair PrintVisitor::visit(RelationalPropertyApplication& node) {
    print_property_application(node, "RelationalPropertyApplication");
    RETURN_VOID;
  }

  z3pair PrintVisitor::visit(SpecPropertyApplication& node) {
    print_property_application(node, "SpecPropertyApplication");
    RETURN_VOID;
  }
}
