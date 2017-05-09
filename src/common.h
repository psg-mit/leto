#pragma once

#include <z3++.h>

#define NO_CHECK_CONTEXT

enum operator_t {PLUS,
                 MINUS,
                 TIMES,
                 DIV,
                 OMINUS,
                 OPLUS,
                 OTIMES,
                 ODIV,
                 FREAD,
                 FWRITE};
enum type_t {INT, FLOAT, BOOL, REAL};

z3::expr* binop(z3::context* context,
                operator_t op,
                type_t type,
                z3::expr* lhs,
                z3::expr* rhs);

z3::expr* float_val(z3::context* context, float val);
