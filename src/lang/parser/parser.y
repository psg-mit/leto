%filenames parser
%scanner ../lexer/scanner.h
%class-name LangParser
%debug


%token NUMBER
       WHILE
       ID
       IF
       ELSE
       INT
       FLOAT
       REAL
       BOOL
       MATRIX
       LMATRIX
       ORIGINAL
       RELAXED
       DECIMAL
       MODEL
       TRUE
       FALSE
       NORMAL
       SKIP
       ASSERT
       ASSUME
       REL_ASSUME
       REL_ASSERT
       FAIL
       COPY
       POW
       FORALL
       FREAD
       FWRITE
       FOR
       INCR
       DECR
       OINCR
       ODECR
       SPECVAR


%left ';'
%left AND OR
%left EQUALS NEQ LT IMPLIES LTEQ
%left '^'
%left '+' '-' OMINUS OPLUS
%left '*' '/' OTIMES ODIV

%polymorphic EXP: lang::Expression*;
             STMT: lang::Statement*;
             VAR: lang::Var*;
             BOOL: lang::BoolExp*;
             RELEXP: lang::RelationalExp*;
             RELBOOL: lang::RelationalBoolExp*;
             SIZE: int;
             EXPLST: lang::ExprList*;
             DECL: lang::Declare*;
             DECLMAT: lang::DeclareMat*;

%type <EXP>  expression
%type <STMT> statement
%type <VAR>  var
%type <BOOL> boolexp
%type <RELEXP> relexpression
%type <RELBOOL> relboolexp
%type <SIZE> size
%type <EXPLST> exprlist
%type <DECL> declare
%type <DECLMAT> declaremat

%%

program:
  expression
| statement
;


expression:
  expression '+' expression {
    $$ = new lang::BinOp(PLUS, $1, $3);
    lang_ast = $$;
  }
| expression '-' expression {
    $$ = new lang::BinOp(MINUS, $1, $3);
    lang_ast = $$;
  }
| expression '*' expression {
    $$ = new lang::BinOp(TIMES, $1, $3);
    lang_ast = $$;
  }
| expression '/' expression {
    $$ = new lang::BinOp(DIV, $1, $3);
    lang_ast = $$;
  }
| '(' expression ')' {
    $$ = $2;
    lang_ast = $$;
  }
| expression OMINUS expression {
    $$ = new lang::BinOp(operator_t::OMINUS, $1, $3);
    lang_ast = $$;
  }
| expression OPLUS expression {
    $$ = new lang::BinOp(operator_t::OPLUS, $1, $3);
    lang_ast = $$;
  }
| expression OTIMES expression {
    $$ = new lang::BinOp(operator_t::OTIMES, $1, $3);
    lang_ast = $$;
  }
| expression ODIV expression {
    $$ = new lang::BinOp(operator_t::ODIV, $1, $3);
    lang_ast = $$;
  }
| NUMBER {
    $$ = new lang::Int(stoi(d_scanner.matched()));
    lang_ast = $$;
  }
| TRUE {
    $$ = new lang::Bool(true);
    lang_ast = $$;
  }
| FALSE {
    $$ = new lang::Bool(false);
    lang_ast = $$;
  }
| REAL '(' size ',' size ')' {
    $$ = new lang::Real($3, $5);
    lang_ast = $$;
  }
| POW '(' expression ',' expression ')' {
    $$ = new lang::Exponent($3, $5);
    lang_ast = $$;
  }
| DECIMAL 'f' {
    $$ = new lang::Float(stof(d_scanner.matched()));
    lang_ast = $$;
  }
| MODEL var {
    $$ = new lang::ModelDeref($2);
    lang_ast = $$;
  }
| FREAD '(' expression ')' {
    $$ = new lang::FaultyRead($3);
    lang_ast = $$;
  }
| var
| var '[' expression ']' {
    $$ = new lang::ArrayAccess($1, {$3});
    lang_ast = $$;
  }
| var '[' expression ']' '[' expression ']' {
    $$ = new lang::ArrayAccess($1, {$3, $6});
    lang_ast = $$;
  }
;

exprlist:
  expression ',' exprlist {
    $$ = new lang::ExprList($1, $3);
    lang_ast = $$;
  }
| expression {
    $$ = new lang::ExprList($1, nullptr);
    lang_ast = $$;
  }
;


var:
  ID {
    $$ = new lang::Var(d_scanner.matched());
    lang_ast = $$;
  }
;

boolexp:
  boolexp '^' boolexp {
    $$ = new lang::BoolExp(lang::XOR, $1, $3);
    lang_ast = $$;
  }
| expression EQUALS expression {
    $$ = new lang::BoolExp(lang::bool_t::EQUALS, $1, $3);
    lang_ast = $$;
  }
| expression LT expression {
    $$ = new lang::BoolExp(lang::bool_t::LT , $1, $3);
    lang_ast = $$;
  }
| expression LTEQ expression {
    $$ = new lang::BoolExp(lang::bool_t::LTEQ , $1, $3);
    lang_ast = $$;
  }
| expression LT expression LT expression {
    lang::BoolExp* lhs = new lang::BoolExp(lang::bool_t::LT, $1, $3);
    lang::BoolExp* rhs = new lang::BoolExp(lang::bool_t::LT, $3, $5);
    $$ = new lang::BoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| expression LTEQ expression LT expression {
    lang::BoolExp* lhs = new lang::BoolExp(lang::bool_t::LTEQ, $1, $3);
    lang::BoolExp* rhs = new lang::BoolExp(lang::bool_t::LT, $3, $5);
    $$ = new lang::BoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| expression LT expression LTEQ expression {
    lang::BoolExp* lhs = new lang::BoolExp(lang::bool_t::LT, $1, $3);
    lang::BoolExp* rhs = new lang::BoolExp(lang::bool_t::LTEQ, $3, $5);
    $$ = new lang::BoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| expression LTEQ expression LTEQ expression {
    lang::BoolExp* lhs = new lang::BoolExp(lang::bool_t::LTEQ, $1, $3);
    lang::BoolExp* rhs = new lang::BoolExp(lang::bool_t::LTEQ, $3, $5);
    $$ = new lang::BoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| expression NEQ expression {
    $$ = new lang::BoolExp(lang::bool_t::NEQ, $1, $3);
    lang_ast = $$;
  }
| boolexp AND boolexp {
    $$ = new lang::BoolExp(lang::bool_t::AND, $1, $3);
    lang_ast = $$;
  }
| boolexp OR boolexp {
    $$ = new lang::BoolExp(lang::bool_t::OR, $1, $3);
    lang_ast = $$;
  }
| boolexp IMPLIES boolexp {
    $$ = new lang::BoolExp(lang::bool_t::IMPLIES, $1, $3);
    lang_ast = $$;
  }
;

relexpression:
  var ORIGINAL {
    $$ = new lang::RelationalVar(lang::relation_t::ORIGINAL, $1);
    lang_ast = $$;
  }
| var RELAXED {
    $$ = new lang::RelationalVar(lang::relation_t::RELAXED, $1);
    lang_ast = $$;
  }
| var {
    $$ = new lang::SpecVar($1);
    lang_ast = $$;
  }
| MODEL var {
    $$ = new lang::RelationalModelDeref($2);
    lang_ast = $$;
  }
| '(' relexpression ')' {
    $$ = $2;
    lang_ast = $$;
  }
| var '[' relexpression ']' {
    $$ = new lang::SpecArrayAccess($1, {$3});
    lang_ast = $$;
  }
| var '[' relexpression ']' '[' relexpression ']' {
    $$ = new lang::SpecArrayAccess($1, {$3, $6});
    lang_ast = $$;
  }
|  var ORIGINAL '[' relexpression ']' {
    $$ = new lang::RelationalArrayAccess(lang::relation_t::ORIGINAL, $1, {$4});
    lang_ast = $$;
  }
| var RELAXED '[' relexpression ']' {
    $$ = new lang::RelationalArrayAccess(lang::relation_t::RELAXED, $1, {$4});
    lang_ast = $$;
  }
|  var ORIGINAL '[' relexpression ']' '[' relexpression ']' {
    $$ = new lang::RelationalArrayAccess(lang::relation_t::ORIGINAL, $1, {$4, $7});
    lang_ast = $$;
  }
| var RELAXED '[' relexpression ']' '[' relexpression ']' {
    $$ = new lang::RelationalArrayAccess(lang::relation_t::RELAXED, $1, {$4, $7});
    lang_ast = $$;
  }
| relexpression '+' relexpression {
    $$ = new lang::RelationalBinOp(PLUS, $1, $3);
    lang_ast = $$;
  }
| relexpression '-' relexpression {
    $$ = new lang::RelationalBinOp(MINUS, $1, $3);
    lang_ast = $$;
  }
| relexpression '*' relexpression {
    $$ = new lang::RelationalBinOp(TIMES, $1, $3);
    lang_ast = $$;
  }
| relexpression '/' relexpression {
    $$ = new lang::RelationalBinOp(DIV, $1, $3);
    lang_ast = $$;
  }
| NUMBER {
    $$ = new lang::RelationalInt(stoi(d_scanner.matched()));
    lang_ast = $$;
  }
| REAL '(' size ',' size ')' {
    $$ = new lang::RelationalReal($3, $5);
    lang_ast = $$;
  }
| DECIMAL 'f' {
    $$ = new lang::RelationalFloat(stof(d_scanner.matched()));
    lang_ast = $$;
  }
| TRUE {
    $$ = new lang::RelationalBool(true);
    lang_ast = $$;
  }
| FALSE {
    $$ = new lang::RelationalBool(false);
    lang_ast = $$;
  }
;

relboolexp:
  relexpression '^' relexpression {
    $$ = new lang::RelationalBoolExp(lang::XOR, $1, $3);
    lang_ast = $$;
  }
| relexpression EQUALS relexpression {
    $$ = new lang::RelationalBoolExp(lang::bool_t::EQUALS, $1, $3);
    lang_ast = $$;
  }
| relexpression NEQ relexpression {
    $$ = new lang::RelationalBoolExp(lang::bool_t::NEQ, $1, $3);
    lang_ast = $$;
  }
| relboolexp AND relboolexp {
    $$ = new lang::RelationalBoolExp(lang::bool_t::AND, $1, $3);
    lang_ast = $$;
  }
| relboolexp OR relboolexp {
    $$ = new lang::RelationalBoolExp(lang::bool_t::OR, $1, $3);
    lang_ast = $$;
  }
| NORMAL '(' relexpression ')' {
    $$ = new lang::RelationalNormal($3);
    lang_ast = $$;
  }
| relboolexp IMPLIES relboolexp {
    $$ = new lang::RelationalBoolExp(lang::bool_t::IMPLIES, $1, $3);
    lang_ast = $$;
  }
| relexpression LT relexpression {
    $$ = new lang::RelationalBoolExp(lang::bool_t::LT, $1, $3);
    lang_ast = $$;
  }
| relexpression LTEQ relexpression {
    $$ = new lang::RelationalBoolExp(lang::bool_t::LTEQ, $1, $3);
    lang_ast = $$;
  }
| relexpression LT relexpression LT relexpression {
    lang::RelationalBoolExp* lhs = new lang::RelationalBoolExp(lang::bool_t::LT, $1, $3);
    lang::RelationalBoolExp* rhs = new lang::RelationalBoolExp(lang::bool_t::LT, $3, $5);
    $$ = new lang::RelationalBoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| relexpression LTEQ relexpression LT relexpression {
    lang::RelationalBoolExp* lhs = new lang::RelationalBoolExp(lang::bool_t::LTEQ, $1, $3);
    lang::RelationalBoolExp* rhs = new lang::RelationalBoolExp(lang::bool_t::LT, $3, $5);
    $$ = new lang::RelationalBoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| relexpression LT relexpression LTEQ relexpression {
    lang::RelationalBoolExp* lhs = new lang::RelationalBoolExp(lang::bool_t::LT, $1, $3);
    lang::RelationalBoolExp* rhs = new lang::RelationalBoolExp(lang::bool_t::LTEQ, $3, $5);
    $$ = new lang::RelationalBoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| relexpression LTEQ relexpression LTEQ relexpression {
    lang::RelationalBoolExp* lhs = new lang::RelationalBoolExp(lang::bool_t::LTEQ, $1, $3);
    lang::RelationalBoolExp* rhs = new lang::RelationalBoolExp(lang::bool_t::LTEQ, $3, $5);
    $$ = new lang::RelationalBoolExp(lang::bool_t::AND, lhs, rhs);
    lang_ast = $$;
  }
| '(' relboolexp ')' {
    $$ = $2;
    lang_ast = $$;
  }
| FORALL '(' var ')' '(' relboolexp ')' {
    $$ = new lang::RelationalForall($3, $6);
    lang_ast = $$;
  }
;

size:
  NUMBER {
    $$ = stoi(d_scanner.matched());
  }
;

declare:
  INT var {
    $$ = new lang::Declare(type_t::INT, $2);
    lang_ast = $$;
  }
| FLOAT var {
    $$ = new lang::Declare(type_t::FLOAT, $2);
    lang_ast = $$;
  }
| REAL var {
    $$ = new lang::Declare(type_t::REAL , $2);
    lang_ast = $$;
  }
| BOOL var {
    $$ = new lang::Declare(type_t::BOOL, $2);
    lang_ast = $$;
  }
;

declaremat:
  MATRIX INT '>' var '(' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::INT, $4, {$6});
    lang_ast = $$;
  }
| MATRIX FLOAT '>' var '(' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::FLOAT, $4, {$6});
    lang_ast = $$;
  }
| MATRIX FLOAT '>' var '(' relexpression ',' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::FLOAT, $4, {$6, $8});
    lang_ast = $$;
  }
| MATRIX INT '>' var '(' relexpression ',' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::INT, $4, {$6, $8});
    lang_ast = $$;
  }
| MATRIX REAL '>' var '(' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::REAL , $4, {$6});
    lang_ast = $$;
  }
| MATRIX REAL '>' var '(' relexpression ',' relexpression ')' {
    $$ = new lang::DeclareMat(type_t::REAL , $4, {$6, $8});
    lang_ast = $$;
  }
;

statement:
  WHILE '(' boolexp ')'
        '(' relboolexp ')'
        '{' statement '}' {
    $$ = new lang::While($3, $6, $9);
    lang_ast = $$;
  }
| FOR '(' statement ';' boolexp ';' statement ')'
      '(' relboolexp ')'
      '{' statement '}' {
    lang::Statement* body = new StatementList($13, $7);
    lang::While* desugar_while = new lang::While($5, $10, body);
    $$ = new lang::StatementList($3, desugar_while);
    lang_ast = $$;
  }
| ASSERT '(' boolexp ')' {
    $$ = new lang::Assert($3);
    lang_ast = $$;
  }
| ASSUME '(' boolexp ')' {
    $$ = new lang::Assert($3);
    lang_ast = $$;
  }
| REL_ASSUME '(' relboolexp ')' {
    $$ = new lang::RelationalAssume($3);
    lang_ast = $$;
  }
| REL_ASSERT '(' relboolexp ')' {
    $$ = new lang::RelationalAssert($3);
    lang_ast = $$;
  }
| FAIL '(' boolexp ')' {
    $$ = new lang::Fail($3);
    lang_ast = $$;
  }
| IF '(' boolexp ')' '{' statement '}' ELSE '{' statement '}' {
    $$ = new lang::If($3, $6, $10);
    lang_ast = $$;
  }
| IF '(' boolexp ')' '{' statement '}' {
    $$ = new lang::If($3, $6, new lang::Skip());
    lang_ast = $$;
  }
| statement ';' statement {
    $$ = new lang::StatementList($1, $3);
    lang_ast = $$;
  }
| expression '=' expression {
    $$ = new lang::Assign($1, $3);
    lang_ast = $$;
  }
| expression '=' boolexp {
    $$ = new lang::Assign($1, $3);
    lang_ast = $$;
  }
| expression '=' '{' exprlist '}' {
    $$ = new lang::ArrayAssign($1, $4);
    lang_ast = $$;
  }
| expression INCR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::PLUS, $1, &ONE));
    lang_ast = $$;
  }
| expression OINCR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::OPLUS, $1, &ONE));
    lang_ast = $$;
  }
| expression DECR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::MINUS, $1, &ONE));
    lang_ast = $$;
  }
| expression ODECR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::OMINUS, $1, &ONE));
    lang_ast = $$;
  }
| INCR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::PLUS, $2, &ONE));
    lang_ast = $$;
  }
| OINCR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::OPLUS, $2, &ONE));
    lang_ast = $$;
  }
| DECR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::MINUS, $2, &ONE));
    lang_ast = $$;
  }
| ODECR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::OMINUS, $2, &ONE));
    lang_ast = $$;
  }
| COPY '(' var ',' var ')' {
    $$ = new lang::Copy($3, $5);
    lang_ast = $$;
  }
| FWRITE '(' expression ',' expression ')' {
    $$ = new lang::FaultyWrite($3, $5);
    lang_ast = $$;
  }
| declare
| SPECVAR declare {
    $2->specvar = true;
    $$ = $2;
    lang_ast = $$;
  }
| declare '=' expression {
    $$ = new lang::StatementList($1, new lang::Assign($1->var, $3));
    lang_ast = $$;
  }
| SPECVAR declare '=' expression {
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::Assign($2->var, $4));
    lang_ast = $$;
  }
| declare '=' boolexp {
    $$ = new lang::StatementList($1, new lang::Assign($1->var, $3));
    lang_ast = $$;
  }
| SPECVAR declare '=' boolexp {
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::Assign($2->var, $4));
    lang_ast = $$;
  }
| declaremat
| SPECVAR declaremat {
    $2->specvar = true;
    $$ = $2;
    lang_ast = $$;
  }
| declaremat '=' '{' exprlist '}' {
    $$ = new lang::StatementList($1, new lang::ArrayAssign($1->var, $4));
    lang_ast = $$;
  }
| SPECVAR declaremat '=' '{' exprlist '}' {
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::ArrayAssign($2->var, $5));
    lang_ast = $$;
  }
| LMATRIX INT '>' var '(' size ')' {
    $$ = new lang::DeclareLMat(type_t::INT, $4, {$6});
    lang_ast = $$;
  }
| LMATRIX FLOAT '>' var '(' size ')' {
    $$ = new lang::DeclareLMat(type_t::FLOAT, $4, {$6});
    lang_ast = $$;
  }
| LMATRIX FLOAT '>' var '(' size ',' size ')' {
    $$ = new lang::DeclareLMat(type_t::FLOAT, $4, {$6, $8});
    lang_ast = $$;
  }
| LMATRIX INT '>' var '(' size ',' size ')' {
    $$ = new lang::DeclareLMat(type_t::INT, $4, {$6, $8});
    lang_ast = $$;
  }
| LMATRIX REAL '>' var '(' size ')' {
    $$ = new lang::DeclareLMat(type_t::REAL , $4, {$6});
    lang_ast = $$;
  }
| LMATRIX REAL '>' var '(' size ',' size ')' {
    $$ = new lang::DeclareLMat(type_t::REAL , $4, {$6, $8});
    lang_ast = $$;
  }
| SKIP {
    $$ = new lang::Skip();
    lang_ast = $$;
  }
;
