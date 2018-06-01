#include "common.h"
#include "lang/CHLVisitor.h"

z3::expr* binop(z3::context* context,
                operator_t op,
                type_t type,
                z3::expr* lhs,
                z3::expr* rhs) {
  Z3_ast rm = Z3_mk_fpa_rne(*context);
  z3::expr *res = nullptr;
  switch (op) {
    case RPLUS:
    case OPLUS:
      switch (type) {
        case INT:
        case REAL:
        case UINT:
          res = new z3::expr(*lhs + *rhs);
          break;
        case FLOAT:
          {
            // std::cout << *lhs << " " << lhs << " " << context << "\n";
            // res = new z3::expr(*lhs + *rhs);
            // I think you can add those contraints here of the limit thing. 
            // Have a clone for each variable, set it to be within limits and then send it to z3 as a constrain. 
            // we can use the same clone variable as clone.
            // z3::expr *n1 = new z3::expr(real_const(name.c_str()));
            // tmp = lhs;
            // std::cout <<  tmp << " " << tmp.substr(0, tmp.size() - 2) + "_tmp" << "\n";
            // std::cout << float_pairs[lhs] << "\n";
            // for (auto& x: lang::CHLVisitor::float_pairs) {
            //   std::cout << x.first << ": " << x.second << std::endl;
            // }
            // std::cout << lang::CHLVisitor::float_pairs.size() << "\n";
            // z3::expr* x = lang::CHLVisitor::float_pairs.at(lhs);
            // // lang::CHLVisitor c;
            // // c.lang::CHLVisitor::add_constraint(*lhs <= 5 )
            // // add_constraint(*lhs + (float_error_range[lhs] * epsilon) >= x )
            // std::cout << lang::CHLVisitor::float_pairs.at(lhs) << "\n";
            std::string upper_lhs;
            if (lang::CHLVisitor::float_clones.find(lhs) == lang::CHLVisitor::float_clones.end() ) {
                upper_lhs = "tmp" + std::to_string(temporary_float_counter);
                temporary_float_counter += 1;
                lang::CHLVisitor::float_clones[lhs] = upper_lhs;
              }
            else{
              upper_lhs = lang::CHLVisitor::float_clones.at(lhs);
            }
            z3::expr* n1 = new z3::expr(context->real_const(upper_lhs.c_str()));
            lang::CHLVisitor::add_constraint(z3::operator<=(z3::operator-(*lhs, (lang::CHLVisitor::float_error_range[lhs] * epsilon)), *n1));   // this adds the constraint
            lang::CHLVisitor::add_constraint(z3::operator>=(z3::operator+(*lhs, (lang::CHLVisitor::float_error_range[lhs] * epsilon)), *n1));   // this adds the constraint
            
            std::string upper_rhs;
            if (lang::CHLVisitor::float_clones.find(rhs) == lang::CHLVisitor::float_clones.end() ) {
                upper_rhs = "tmp" + std::to_string(temporary_float_counter);
                temporary_float_counter += 1;
                lang::CHLVisitor::float_clones[rhs] = upper_rhs;
              }
            else{
              upper_rhs = lang::CHLVisitor::float_clones.at(rhs);
            }
            z3::expr* n2 = new z3::expr(context->real_const(upper_rhs.c_str()));
            lang::CHLVisitor::add_constraint(z3::operator<=(z3::operator-(*lhs, (lang::CHLVisitor::float_error_range[lhs] * epsilon)), *n2));   // this adds the constraint
            lang::CHLVisitor::add_constraint(z3::operator>=(z3::operator+(*lhs, (lang::CHLVisitor::float_error_range[lhs] * epsilon)), *n2));   // this adds the constraint

            res = new z3::expr(*n1 + *n2);
            // assert(0);
            // Z3_ast prim = Z3_mk_fpa_add(*context, rm, *lhs, *rhs);
            // res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case RMINUS:
    case OMINUS:
      switch (type) {
        case INT:
        case REAL:
        case UINT:
          res = new z3::expr(*lhs - *rhs);
          break;
        case FLOAT:
          {
            assert(0);
            Z3_ast prim = Z3_mk_fpa_sub(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case RTIMES:
    case OTIMES:
      switch (type) {
        case INT:
        case REAL:
        case UINT:
          res = new z3::expr(*lhs * *rhs);
          break;
        case FLOAT:
          {
            assert(0);
            Z3_ast prim = Z3_mk_fpa_mul(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case RDIV:
    case ODIV:
      switch(type) {
        case INT:
        case REAL:
        case UINT:
          res = new z3::expr(*lhs / *rhs);
          break;
        case FLOAT:
          {
            assert(0);
            Z3_ast prim = Z3_mk_fpa_div(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case FREAD:
    case FWRITE:
      assert(false);
      break;
  }

  assert(res);
  return res;
}

z3::expr* float_val(z3::context* context, float val) {
  assert(0);
  Z3_sort fl = Z3_mk_fpa_sort_single(*context);
  Z3_ast float_val = Z3_mk_fpa_numeral_float(*context, val, fl);
  return new z3::expr(z3::to_expr(*context, float_val));
}
