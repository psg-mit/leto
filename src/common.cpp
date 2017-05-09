#include "common.h"

z3::expr* binop(z3::context* context,
                operator_t op,
                type_t type,
                z3::expr* lhs,
                z3::expr* rhs) {
  Z3_ast rm = Z3_mk_fpa_rne(*context);
  z3::expr *res = nullptr;
  switch (op) {
    case PLUS:
    case OPLUS:
      switch (type) {
        case INT:
        case REAL:
          res = new z3::expr(*lhs + *rhs);
          break;
        case FLOAT:
          {
            Z3_ast prim = Z3_mk_fpa_add(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case MINUS:
    case OMINUS:
      switch (type) {
        case INT:
        case REAL:
          res = new z3::expr(*lhs - *rhs);
          break;
        case FLOAT:
          {
            Z3_ast prim = Z3_mk_fpa_sub(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case TIMES:
    case OTIMES:
      switch (type) {
        case INT:
        case REAL:
          res = new z3::expr(*lhs * *rhs);
          break;
        case FLOAT:
          {
            Z3_ast prim = Z3_mk_fpa_mul(*context, rm, *lhs, *rhs);
            res = new z3::expr(z3::to_expr(*context, prim));
          }
          break;
        case BOOL:
          assert(false);
          break;
      }
      break;
    case DIV:
    case ODIV:
      switch(type) {
        case INT:
        case REAL:
          res = new z3::expr(*lhs / *rhs);
          break;
        case FLOAT:
          {
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
  Z3_sort fl = Z3_mk_fpa_sort_single(*context);
  Z3_ast float_val = Z3_mk_fpa_numeral_float(*context, val, fl);
  return new z3::expr(z3::to_expr(*context, float_val));
}
