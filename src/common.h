#pragma once

#include <unordered_map>

#include <z3++.h>

#define NO_CHECK_CONTEXT

#define RETURN_VOID return {nullptr, nullptr}

typedef std::unordered_map<std::string, unsigned> version_map;


enum operator_t {RPLUS,
                 RMINUS,
                 RTIMES,
                 RDIV,
                 OMINUS,
                 OPLUS,
                 OTIMES,
                 ODIV,
                 FREAD,
                 FWRITE};
enum type_t {INT, FLOAT, BOOL, REAL, UINT};

z3::expr* binop(z3::context* context,
                operator_t op,
                type_t type,
                z3::expr* lhs,
                z3::expr* rhs);

z3::expr* float_val(z3::context* context, float val);

static double epsilon = 0.005;
static int temporary_float_counter = 0;             // this maintains the counter for floating numbers
// static std::unordered_map<z3::expr*, z3::expr*> float_pairs;   // this is for the x:(oexpr, oexpr_1) pairs
// static std::unordered_map<z3::expr*, int> float_error_range;
// std::unordered_map<std::string, std::string> float_clones;  // clones for floating numbers, not needed, I can do it with the _upp variable

