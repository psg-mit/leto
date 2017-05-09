#include "LangNodes.h"
#include "PrintVisitor.h"

#include "lexer/scanner.h"
#include "parser/parser.h"


extern lang::LangNode *lang_ast;

int main() {
  lang::LangParser test;
  int ret = test.parse();

  lang::PrintVisitor printer;
  lang_ast->accept(printer);

  return ret;
}
