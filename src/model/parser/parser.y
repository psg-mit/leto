%filenames parser
%scanner ../lexer/scanner.h
%class-name ModelParser
%debug


%token NUMBER
       ID
       TRUE
       FALSE
       BOOL
       OPERATOR
       WHEN
       ENSURES
       DECIMAL
       NIL
       MODIFIES
       FREAD
       FWRITE

%left ';'
%left AND
%left EQUALS '<' LTEQ
%left '+' '-'
%left '*' '/'

%polymorphic EXP:     model::Expression*;
             VAR:     model::Var*;
             STMT:    model::Statement*;
             BOOLEXP: model::BoolExp*;
             VARLIST: model::VarList*

%type <EXP>     expression
%type <VAR>     var
%type <STMT>    statement
%type <BOOLEXP> boolexp
%type <VARLIST> varlist

%%

program: expression | statement;

expression:
  NUMBER {
    $$ = new model::Int(stoi(d_scanner.matched()));
    model_ast = $$;
  }
| expression '+' expression {
    $$ = new model::BinOp(PLUS, $1, $3);
    model_ast = $$;
  }
| expression '-' expression {
    $$ = new model::BinOp(MINUS, $1, $3);
    model_ast = $$;
  }
| expression '*' expression {
    $$ = new model::BinOp(TIMES, $1, $3);
    model_ast = $$;
  }
| expression '/' expression {
    $$ = new model::BinOp(DIV, $1, $3);
    model_ast = $$;
  }
| var
| boolexp
| DECIMAL {
    $$ = new model::Float(stof(d_scanner.matched()));
    model_ast = $$;
  }
;

boolexp:
  TRUE {
    $$ = new model::Bool(true);
    model_ast = $$;
  }
| FALSE {
    $$ = new model::Bool(false);
    model_ast = $$;
  }
| expression EQUALS expression {
    $$ = new model::BoolBinOp(model::bool_t::EQUALS, $1, $3);
    model_ast = $$;
  }
| expression AND expression {
    $$ = new model::BoolBinOp(model::bool_t::AND, $1, $3);
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
| statement ';' statement {
    $$ = new model::StatementList($1, $3);
    model_ast = $$;
  }
| var '=' expression {
    $$ = new model::Assign($1, $3);
    model_ast = $$;
  }
| OPERATOR '+' '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(PLUS, $4, $6, $10, $14, $18);
    model_ast = $$;
  }
| OPERATOR '-' '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(MINUS, $4, $6, $10, $14, $18);
    model_ast = $$;
  }
| OPERATOR '*' '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(TIMES, $4, $6, $10, $14, $18);
    model_ast = $$;
  }
| OPERATOR '/' '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(DIV, $4, $6, $10, $14, $18);
    model_ast = $$;
  }
| FREAD '(' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FREAD, $3, nullptr, $7, $11, $15);
    model_ast = $$;
  }
| FWRITE '(' var ',' var ')'
  WHEN '(' boolexp ')'
  MODIFIES '(' varlist ')'
  ENSURES '(' boolexp ')' {
    $$ = new model::Operator(operator_t::FWRITE, $3, $5, $9, $13, $17);
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
| NIL {
    $$ = nullptr;
    model_ast = $$;
  }
;
