%filenames parser
%scanner ../lexer/scanner.h
%class-name ModelParser
%debug


%token NUMBER
       ID
       TRUE
       FALSE
       BOOL
       INT
       REAL
       OPERATOR
       WHEN
       ENSURES
       DECIMAL
       MODIFIES
       FREAD
       FWRITE
       OLD
       REGION
       BEGIN_COMMIT
       END_COMMIT
       STEP
       THROWS
       POWERON

%left ';'
%left AND OR
%left EQUALS '<' LTEQ
%left '+' '-'
%left '*' '/'

%polymorphic EXP:     model::Expression*;
             VAR:     model::Var*;
             STMT:    model::Statement*;
             BOOLEXP: model::BoolExp*;
             VARLIST: model::VarList*;
             OP:      operator_t;
             SIZE:    int;

%type <OP>      op
%type <EXP>     expression
%type <VAR>     var
%type <STMT>    statement
%type <BOOLEXP> boolexp
%type <VARLIST> varlist
%type <SIZE> size

%%

program: expression | statement;

op:
  '+' { $$ = RPLUS; }
| '-' { $$ = RMINUS; }
| '*' { $$ = RTIMES; }
| '/' { $$ = RDIV; }
;

size:
  NUMBER {
    $$ = stoi(d_scanner.matched());
  }
;

expression:
  NUMBER {
    $$ = new model::Int(stoi(d_scanner.matched()));
    model_ast = $$;
  }
| expression '+' expression {
    $$ = new model::BinOp(OPLUS, $1, $3);
    model_ast = $$;
  }
| expression '-' expression {
    $$ = new model::BinOp(OMINUS, $1, $3);
    model_ast = $$;
  }
| expression '*' expression {
    $$ = new model::BinOp(OTIMES, $1, $3);
    model_ast = $$;
  }
| expression '/' expression {
    $$ = new model::BinOp(ODIV, $1, $3);
    model_ast = $$;
  }
| '-' expression {
    $$ = new model::BinOp(OMINUS, &ZERO, $2);
    model_ast = $$;
  }
| var
| DECIMAL {
    $$ = new model::Float(stof(d_scanner.matched()));
    model_ast = $$;
  }
| TRUE {
    $$ = new model::Bool(true);
    model_ast = $$;
  }
| FALSE {
    $$ = new model::Bool(false);
    model_ast = $$;
  }
| OLD '(' var ')' {
    $$ = new model::Old($3);
    model_ast = $$;
  }
| '(' expression ')' {
    $$ = $2;
    model_ast = $$;
  }
| REAL '(' size ',' size ')' {
    $$ = new model::Real($3, $5);
    model_ast = $$;
  }
;

boolexp:
  expression EQUALS expression {
    $$ = new model::BoolBinOp(model::bool_t::EQUALS, $1, $3);
    model_ast = $$;
  }
| boolexp AND boolexp {
    $$ = new model::BoolBinOp(model::bool_t::AND, $1, $3);
    model_ast = $$;
  }
| boolexp OR boolexp {
    $$ = new model::BoolBinOp(model::bool_t::OR , $1, $3);
    model_ast = $$;
  }
| expression '<' expression {
    $$ = new model::BoolBinOp(model::bool_t::LT, $1, $3);
    model_ast = $$;
  }
| expression LTEQ expression {
    $$ = new model::BoolBinOp(model::bool_t::LTEQ, $1, $3);
    model_ast = $$;
  }
| expression '<' expression '<' expression {
    model::BoolBinOp* lhs = new model::BoolBinOp(model::bool_t::LT, $1, $3);
    model::BoolBinOp* rhs = new model::BoolBinOp(model::bool_t::LT, $3, $5);
    $$ = new model::BoolBinOp(model::bool_t::AND, lhs, rhs);
    model_ast = $$;
  }
| expression LTEQ expression '<' expression {
    model::BoolBinOp* lhs = new model::BoolBinOp(model::bool_t::LTEQ, $1, $3);
    model::BoolBinOp* rhs = new model::BoolBinOp(model::bool_t::LT, $3, $5);
    $$ = new model::BoolBinOp(model::bool_t::AND, lhs, rhs);
    model_ast = $$;
  }
| expression '<' expression LTEQ expression {
    model::BoolBinOp* lhs = new model::BoolBinOp(model::bool_t::LT, $1, $3);
    model::BoolBinOp* rhs = new model::BoolBinOp(model::bool_t::LTEQ, $3, $5);
    $$ = new model::BoolBinOp(model::bool_t::AND, lhs, rhs);
    model_ast = $$;
  }
| expression LTEQ expression LTEQ expression {
    model::BoolBinOp* lhs = new model::BoolBinOp(model::bool_t::LTEQ, $1, $3);
    model::BoolBinOp* rhs = new model::BoolBinOp(model::bool_t::LTEQ, $3, $5);
    $$ = new model::BoolBinOp(model::bool_t::AND, lhs, rhs);
    model_ast = $$;
  }
| '(' boolexp ')' {
    $$ = $2;
    model_ast = $$;
  }
;

statement:
  BOOL var {
    $$ = new model::Declare(type_t::BOOL, $2);
    model_ast = $$;
  }
| BOOL var '=' expression {
    $$ = new model::StatementList(new model::Declare(type_t::BOOL, $2),
                                  new model::Assign($2, $4));
    model_ast = $$;
  }
| INT var {
    $$ = new model::Declare(type_t::INT, $2);
    model_ast = $$;
  }
| INT var '=' expression {
    $$ = new model::StatementList(new model::Declare(type_t::INT, $2),
                                  new model::Assign($2, $4));
    model_ast = $$;
  }
| REAL var {
    $$ = new model::Declare(type_t::REAL, $2);
    model_ast = $$;
  }
| REAL var '=' expression {
    $$ = new model::StatementList(new model::Declare(type_t::REAL, $2),
                                  new model::Assign($2, $4));
    model_ast = $$;
  }
| BOOL var '=' boolexp {
    $$ = new model::StatementList(new model::Declare(type_t::BOOL, $2),
                                  new model::Assign($2, $4));
    model_ast = $$;
  }
| statement ';' statement {
    $$ = new model::StatementList($1, $3);
    model_ast = $$;
  }
| statement ';' {
    $$ = $1;
    model_ast = $$;
  }
| var '=' expression {
    $$ = new model::Assign($1, $3);
    model_ast = $$;
  }
| var '=' boolexp {
    $$ = new model::Assign($1, $3);
    model_ast = $$;
  }
| OPERATOR op '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator($2, $4, $6, $10, $14, $18);
    model_ast = $$;
  }
| BEGIN_COMMIT
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Commit(commit_t::BEGIN, $4, $8);
    model_ast = $$;
}
| END_COMMIT
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Commit(commit_t::END, $4, $8);
    model_ast = $$;
}
| REGION '(' var ')'
  FREAD '(' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FREAD, $7, nullptr, $11, $15, $19);
    model_ast = $$;
  }
| REGION '(' var ')'
  FWRITE '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FWRITE, $7, $9, $13, $17, $21);
    model_ast = $$;
  }
| OPERATOR op '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator($2, $4, $6, $10, nullptr, $17);
    model_ast = $$;
  }
| REGION '(' var ')'
  FREAD '(' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FREAD, $7, nullptr, $11, nullptr, $18);
    model_ast = $$;
  }
| REGION '(' var ')'
  FWRITE '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FWRITE, $7, $9, $13, nullptr, $20);
    model_ast = $$;
  }
| OPERATOR op '(' var ',' var ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator($2, $4, $6, &TRUE_NODE, $10, $14);
    model_ast = $$;
  }
| REGION '(' var ')'
  FREAD '(' var ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FREAD,
                             $7,
                             nullptr,
                             &TRUE_NODE,
                             $11,
                             $15);
    model_ast = $$;
  }
| REGION '(' var ')'
  FWRITE '(' var ',' var ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FWRITE, $7, $9, &TRUE_NODE, $13, $17);
    model_ast = $$;
  }
| OPERATOR op '(' var ',' var ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator($2, $4, $6, &TRUE_NODE, nullptr, $13);
    model_ast = $$;
  }
| REGION '(' var ')'
  FREAD '(' var ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FREAD,
                             $7,
                             nullptr,
                             &TRUE_NODE,
                             nullptr,
                             $14);
    model_ast = $$;
  }
| REGION '(' var ')'
  FWRITE '(' var ',' var ')'
  MODIFIES '(' ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FWRITE,
                             $7,
                             $9,
                             &TRUE_NODE,
                             nullptr,
                             $16);
    model_ast = $$;
  }
| STEP
  WHEN '(' boolexp ')'
  THROWS POWERON
  ENSURES '(' boolexp ')' {
    $$ = new model::Step($4, exception_t::POWERON, $10);
    model_ast = $$;
  }
| STEP
  ENSURES '(' boolexp ')' {
    $$ = new model::Step(&TRUE_NODE, exception_t::NONE, $4);
    model_ast = $$;
  }
| '{' statement '}' {
    $$ = new model::Block($2);
    model_ast = $$;
  }
;

var:
  ID {
    $$ = new model::Var(d_scanner.matched());
    model_ast = $$;
  }
;

varlist:
  var ',' varlist {
    $$ = new model::VarList($1, $3);
    model_ast = $$;
  }
| var {
    $$ = new model::VarList($1, nullptr);
    model_ast = $$;
  }
;
