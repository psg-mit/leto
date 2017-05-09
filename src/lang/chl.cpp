#include <z3++.h>

#include "LangNodes.h"
#include "CHLVisitor.h"

#include "lexer/scanner.h"
#include "parser/parser.h"


extern lang::LangNode *lang_ast;

int main() {
  lang::LangParser test;
  int ret = test.parse();

  z3::context context;
  z3::solver solver(context);

  model::Z3Visitor model_visitor(nullptr, nullptr);

  lang::CHLVisitor chl(&context, &solver, &model_visitor);
  lang_ast->accept(chl);

  chl.check();

  return ret;
}
