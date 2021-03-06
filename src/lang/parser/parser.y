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
       UINT
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
       EXISTS
       FREAD
       FWRITE
       FOR
       INCR
       DECR
       OINCR
       ODECR
       SPECVAR
       NOINF
       EQ
       REQUIRES
       R_REQUIRES
       RETURN
       PROPERTY
       PROPERTY_R
       REGION
       LABEL


%left ';'
%left AND OR '^'
%left EQUALS NEQ LT IMPLIES LTEQ
%left '+' '-' RMINUS RPLUS
%left '*' '/' RTIMES RDIV

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
             VARLIST: lang::VarList*;
             RELVARLIST: lang::RelationalVarList*;
             DECLARELIST: lang::DeclareList*;
             TYPE: type_t;
             RELVAR: lang::RelationalVar*;
             RELMODELDEREF: lang::RelationalModelDeref*;

%type <EXP>  expression
%type <STMT> statement cflow statementlist
%type <VAR>  var
%type <RELVAR> relvar
%type <BOOL> boolexp
%type <RELEXP> relexpression
%type <RELBOOL> relboolexp
%type <SIZE> size
%type <EXPLST> exprlist
%type <DECL> declare singledeclare
%type <DECLMAT> declaremat singledeclaremat
%type <VARLIST> varlist matvarlist
%type <RELVARLIST> relvarlist
%type <DECLARELIST> declarelist
%type <TYPE> type
%type <RELMODELDEREF> relmodelderef;

%%

program:
  expression
| statementlist
;

type:
  FLOAT { $$ = type_t::FLOAT; }
| REAL  { $$ = type_t::REAL;  }
| BOOL  { $$ = type_t::BOOL;  }
| INT   { $$ = type_t::INT;   }
| UINT  { $$ = type_t::UINT;  }
;

expression:
  expression '+' expression {
    $$ = new lang::BinOp(operator_t::OPLUS, $1, $3);
    lang_ast = $$;
  }
| expression '-' expression {
    $$ = new lang::BinOp(operator_t::OMINUS, $1, $3);
    lang_ast = $$;
  }
| expression '*' expression {
    $$ = new lang::BinOp(operator_t::OTIMES, $1, $3);
    lang_ast = $$;
  }
| expression '/' expression {
    $$ = new lang::BinOp(operator_t::ODIV, $1, $3);
    lang_ast = $$;
  }
| '(' expression ')' {
    $$ = $2;
    lang_ast = $$;
  }
| expression RMINUS expression {
    $$ = new lang::BinOp(operator_t::RMINUS, $1, $3);
    lang_ast = $$;
  }
| expression RPLUS expression {
    $$ = new lang::BinOp(operator_t::RPLUS, $1, $3);
    lang_ast = $$;
  }
| expression RTIMES expression {
    $$ = new lang::BinOp(operator_t::RTIMES, $1, $3);
    lang_ast = $$;
  }
| expression RDIV expression {
    $$ = new lang::BinOp(operator_t::RDIV, $1, $3);
    lang_ast = $$;
  }
| '-' expression {
    $$ = new lang::BinOp(operator_t::OMINUS, &ZERO, $2);
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
| '(' boolexp ')' {
  $$ = $2;
  lang_ast = $2;
}
| FORALL '(' type var ')' '(' boolexp ')' {
    $$ = new lang::Forall($3, $4, $7);
    lang_ast = $$;
  }
| var '(' varlist ')' {
    $$ = new lang::PropertyApplication($1, $3);
    lang_ast = $$;
  }
;

relvar:
  var ORIGINAL {
    $$ = new lang::RelationalVar(lang::relation_t::ORIGINAL, $1);
    lang_ast = $$;
  }
| var RELAXED {
    $$ = new lang::RelationalVar(lang::relation_t::RELAXED, $1);
    lang_ast = $$;
  }
;

relmodelderef:
  MODEL var {
    $$ = new lang::RelationalModelDeref($2);
    lang_ast = $$;
  }
;

relexpression:
  relvar
| var {
    $$ = new lang::SpecVar($1);
    lang_ast = $$;
  }
| '-' relexpression {
    $$ = new lang::RelationalBinOp(operator_t::OMINUS, &REL_ZERO, $2);
    lang_ast = $$;
  }
| relmodelderef
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
    $$ = new lang::RelationalBinOp(OPLUS, $1, $3);
    lang_ast = $$;
  }
| relexpression '-' relexpression {
    $$ = new lang::RelationalBinOp(OMINUS, $1, $3);
    lang_ast = $$;
  }
| relexpression '*' relexpression {
    $$ = new lang::RelationalBinOp(OTIMES, $1, $3);
    lang_ast = $$;
  }
| relexpression '/' relexpression {
    $$ = new lang::RelationalBinOp(ODIV, $1, $3);
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
  relboolexp '^' relboolexp {
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
| FORALL '(' type var ')' '(' relboolexp ')' {
    $$ = new lang::RelationalForall($3, $4, $7);
    lang_ast = $$;
  }
| EXISTS '(' type var ')' '(' relboolexp ')' {
    $$ = new lang::RelationalExists($3, $4, $7);
    lang_ast = $$;
  }
| EQ '(' var ')' {
    RelationalVar* ovar = new RelationalVar(lang::relation_t::ORIGINAL, $3);
    RelationalVar* rvar = new RelationalVar(lang::relation_t::RELAXED, $3);
    $$ = new lang::RelationalBoolExp(lang::bool_t::EQUALS, ovar, rvar);
    lang_ast = $$;
  }
| var '(' varlist ')' {
    $$ = new lang::RelationalPropertyApplication($1, $3);
    lang_ast = $$;
  }
| var '(' relvarlist ')' {
    $$ = new lang::SpecPropertyApplication($1, $3);
    lang_ast = $$;
  }
| '!' relboolexp {
    $$ = new lang::RelationalBoolExp(lang::bool_t::EQUALS,
                                     $2,
                                     new lang::RelationalBool(false));
    lang_ast = $$;
  }
;

size:
  NUMBER {
    $$ = stoi(d_scanner.matched());
  }
;

declare:
  type varlist {
    $$ = new lang::Declare($1, $2, nullptr);
    lang_ast = $$;
  }

| REGION '(' var ')' type varlist {
    $$ = new lang::Declare($5, $6, $3);
    lang_ast = $$;
  }
;

declaremat:
  MATRIX type '>' matvarlist {
    $$ = new lang::DeclareMat($2, $4, nullptr);
    lang_ast = $$;
  }
| REGION '(' var ')' MATRIX type '>' matvarlist {
    $$ = new lang::DeclareMat($6, $8, $3);
    lang_ast = $$;
  }
;

singledeclare:
  type var {
    $$ = new lang::Declare($1, new lang::VarList($2, nullptr), nullptr);
    lang_ast = $$;
  }
;

singledeclaremat:
  MATRIX type '>' var {
    $$ = new lang::DeclareMat($2, new lang::VarList($4, {}, nullptr), nullptr);
    lang_ast = $$;
  }
| MATRIX type '>' var '(' expression ')' {
    $$ = new lang::DeclareMat($2, new lang::VarList($4, {$6}, nullptr), nullptr);
    lang_ast = $$;
  }
| MATRIX type '>' var '(' expression ',' expression')' {
    $$ = new lang::DeclareMat($2, new lang::VarList($4, {$6, $8}, nullptr), nullptr);
    lang_ast = $$;
  }
;

cflow:
  LABEL '(' var ')'
  WHILE '(' boolexp ')'
        '(' boolexp ')'
        '(' relboolexp ')'
        '{' statementlist '}' {
    $$ = new lang::While($3, $7, $10, $13, $16, true);
    lang_ast = $$;
  }
| LABEL '(' var ')'
  FOR   '(' statement ';' boolexp ';' statement ')'
        '(' boolexp ')'
        '(' relboolexp ')'
        '{' statementlist '}' {
    lang::Statement* body = new StatementList($20, $11);
    lang::While* desugar_while = new lang::While($3, $9, $14, $17, body, true);
    $$ = new lang::StatementList($7, desugar_while);
    lang_ast = $$;
  }
| NOINF LABEL '(' var ')'
  WHILE '(' boolexp ')'
        '(' boolexp ')'
        '(' relboolexp ')'
        '{' statementlist '}' {
    $$ = new lang::While($4, $8, $11, $14, $17, false);
    lang_ast = $$;
  }
| NOINF LABEL '(' var ')'
  FOR '(' statement ';' boolexp ';' statement ')'
      '(' boolexp ')'
      '(' relboolexp ')'
      '{' statementlist '}' {
    lang::Statement* body = new StatementList($21, $12);
    lang::While* desugar_while = new lang::While($4, $10, $15, $18, body, false);
    $$ = new lang::StatementList($8, desugar_while);
    lang_ast = $$;
  }
| IF '(' boolexp ')' '{' statementlist '}' ELSE '{' statementlist '}' {
    $$ = new lang::If($3, $6, $10);
    lang_ast = $$;
  }
| IF '(' boolexp ')' '{' statementlist '}' {
    $$ = new lang::If($3, $6, new lang::Skip());
    lang_ast = $$;
  }
| REQUIRES boolexp
  R_REQUIRES relboolexp
  type var '(' declarelist ')' '{' statementlist '}' {
    $$ = new lang::Function($2, $4, false, $5, $6, $8, $11);
    lang_ast = $$;
  }
| REQUIRES boolexp
  R_REQUIRES relboolexp
  MATRIX type '>' var '(' declarelist ')' '{' statementlist '}' {
    $$ = new lang::Function($2, $4, true, $6, $8, $10, $13);
    lang_ast = $$;
  }
;


statement:
  PROPERTY var '(' declarelist ')' ':' boolexp {
    $$ = new lang::Property($2, $4, $7);
    lang_ast = $$;
  }
| PROPERTY_R var '(' declarelist ')' ':' relboolexp {
    $$ = new lang::RelationalProperty($2, $4, $7);
    lang_ast = $$;
  }
| RETURN expression {
    $$ = new lang::Return($2);
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
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::RPLUS, $1, &ONE));
    lang_ast = $$;
  }
| expression OINCR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::OPLUS, $1, &ONE));
    lang_ast = $$;
  }
| expression DECR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::RMINUS, $1, &ONE));
    lang_ast = $$;
  }
| expression ODECR {
    $$ = new lang::Assign($1, new lang::BinOp(operator_t::OMINUS, $1, &ONE));
    lang_ast = $$;
  }
| INCR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::RPLUS, $2, &ONE));
    lang_ast = $$;
  }
| OINCR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::OPLUS, $2, &ONE));
    lang_ast = $$;
  }
| DECR expression {
    $$ = new lang::Assign($2, new lang::BinOp(operator_t::RMINUS, $2, &ONE));
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
    assert(!$1->vars->cdr);
    $$ = new lang::StatementList($1, new lang::Assign($1->vars->car, $3));
    lang_ast = $$;
  }
| SPECVAR declare '=' expression {
    assert(!$2->vars->cdr);
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::Assign($2->vars->car, $4));
    lang_ast = $$;
  }
| declare '=' boolexp {
    $$ = new lang::StatementList($1, new lang::Assign($1->vars->car, $3));
    lang_ast = $$;
  }
| SPECVAR declare '=' boolexp {
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::Assign($2->vars->car, $4));
    lang_ast = $$;
  }
| declaremat
| SPECVAR declaremat {
    $2->specvar = true;
    $$ = $2;
    lang_ast = $$;
  }
| declaremat '=' '{' exprlist '}' {
    assert(!$1->vars->cdr);
    $$ = new lang::StatementList($1, new lang::ArrayAssign($1->vars->car, $4));
    lang_ast = $$;
  }
| SPECVAR declaremat '=' '{' exprlist '}' {
    assert(!$2->vars->cdr);
    $2->specvar = true;
    $$ = new lang::StatementList($2, new lang::ArrayAssign($2->vars->car, $5));
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

statementlist:
  cflow
| cflow statementlist {
    $$ = new lang::StatementList($1, $2);
    lang_ast = $$;
  }
| statement ';' statementlist {
    $$ = new lang::StatementList($1, $3);
    lang_ast = $$;
  }
| statement ';' {
    $$ = $1;
    lang_ast = $$;
  }
;

varlist:
  var ',' varlist {
    $$ = new lang::VarList($1, $3);
    lang_ast = $$;
  }
| var {
    $$ = new lang::VarList($1, nullptr);
    lang_ast = $$;
  }
;

relvarlist:
  relvar ',' relvarlist {
    $$ = new lang::RelationalVarList($1, $3);
    lang_ast = $$;
  }
| relvar {
    $$ = new lang::RelationalVarList($1, nullptr);
    lang_ast = $$;
  }
;

matvarlist:
  var '(' expression ')' ',' matvarlist {
    $$ = new lang::VarList($1, {$3}, $6);
    lang_ast = $$;
  }
| var '(' expression ')' {
    $$ = new lang::VarList($1, {$3}, nullptr);
    lang_ast = $$;
  }
| var '(' expression ',' expression ')' ',' matvarlist {
    $$ = new lang::VarList($1, {$3, $5}, $8);
    lang_ast = $$;
  }
| var '(' expression ',' expression ')' {
    $$ = new lang::VarList($1, {$3, $5}, nullptr);
    lang_ast = $$;
  }
;

declarelist:
  singledeclare ',' declarelist {
    $$ = new lang::DeclareList($1, $3);
    lang_ast = $$;
  }
| singledeclare {
    $$ = new lang::DeclareList($1, nullptr);
    lang_ast = $$;
  }
| singledeclaremat ',' declarelist {
    $$ = new lang::DeclareList($1, $3);
    lang_ast = $$;
  }
| singledeclaremat {
    $$ = new lang::DeclareList($1, nullptr);
    lang_ast = $$;
  }
;
