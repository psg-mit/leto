#include "ModelNodes.h"
#include "PrintVisitor.h"

#include "lexer/scanner.h"
#include "parser/parser.h"


extern model::ModelNode *model_ast;

int main() {
  model::ModelParser test;
  int ret = test.parse();

  model::PrintVisitor printer;
  model_ast->accept(printer);

  return ret;
}
