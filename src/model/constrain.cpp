#include <z3++.h>

#include "ModelNodes.h"
#include "Z3Visitor.h"

#include "lexer/scanner.h"
#include "parser/parser.h"


extern model::ModelNode *model_ast;

int main() {
  model::ModelParser test;
  int ret = test.parse();

  z3::context context;
  z3::solver solver(context);

  model::Z3Visitor visitor(&context, &solver);
  model_ast->accept(visitor);

  visitor.check();

  return ret;
}
