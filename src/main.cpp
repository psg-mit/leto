#include <ctime>
#include <fstream>

#include <z3++.h>

#include "common.h"

#include "lang/CHLVisitor.h"
#include "lang/lexer/scanner.h"
#include "lang/parser/parser.h"

#include "model/Z3Visitor.h"
#include "model/lexer/scanner.h"
#include "model/parser/parser.h"

#define Z3_CONSTRAINT_FILE "constraints_z3.smt2"
#define SMT_CONSTRAINT_FILE "constraints_smt2.smt2"


extern lang::LangNode *lang_ast;
extern model::ModelNode *model_ast;

int main() {
  const clock_t start_time = clock();
  // Construct z3 components
  z3::context context;
  z3::solver solver(context);

  // Read model first
  model::ModelParser model_parser;
  int ret = model_parser.parse();
  if (ret) {
    std::cerr << "Failed to parse model" << std::endl;
    return ret;
  }
  model::Z3Visitor model_visitor(&context, &solver);
  model_ast->accept(model_visitor);
  model_visitor.init_vars();
  model_visitor.remove_refined();

  // Read lang
  lang::LangParser lang_parser;
  ret = lang_parser.parse();
  if (ret) {
    std::cerr << "Failed to parse program" << std::endl;
    return ret;
  }

  // Open log files
  std::ofstream z3_log(Z3_CONSTRAINT_FILE, std::ios_base::trunc);
  std::ofstream smt2_log(SMT_CONSTRAINT_FILE, std::ios_base::trunc);

  // Check
  lang::CHLVisitor chl(&context, &solver, &model_visitor, z3_log, smt2_log);
  lang_ast->accept(chl);

  // Close log files
  z3_log.close();
  smt2_log.close();

  int errors = chl.get_errors();
  assert(errors >= 0);

  if (errors > 0) {
    std::cerr << errors
              << " "
              << (errors == 1 ? "error" : "errors")
              << " found"
              << std::endl;
  }

  if (chl.unsat_context) {
    std::cerr << "WARNING: Some contexts were unsatisfiable" << std::endl;
  }

  if (chl.unknown_context) {
    std::cerr << "WARNING: Some contexts were unknown" << std::endl;
  }

#ifdef NO_CHECK_CONTEXT
  std::cerr << "WARNING: Context checks disabled" << std::endl;
#endif

  std::cout << "Time: "
            << static_cast<double>(clock() - start_time) /  CLOCKS_PER_SEC
            << " seconds"
            << std::endl;

  std::cout << "Constraints generated: "
            << chl.constraints_generated
            << std::endl;

  std::cout << "Houdini invariants found: "
            << chl.num_inferred
            << std::endl;

  std::cout << "Total paths: " << chl.total_paths << std::endl;
  std::cout << "Pruned paths: " << chl.pruned_paths << std::endl;

  return chl.get_errors();
}
