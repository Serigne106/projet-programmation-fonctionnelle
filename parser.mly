%{
  open Syntax
%}


%token EOF
%token <int> INT
%token <float> FLOAT
%token <unit> UNIT
%token <Syntax.idvar> VAR
%token EQ
%token PLUS MINUS MULT DIV
%token PLUSPT MINUSPT MULTPT DIVPT
%token LAND LOR NOT PRINTINT
%token NEQ GREAT GREATEQ LESS LESSEQ
%token TRUE FALSE
%token LPAR RPAR COMMA COLON
%token LET IN LETREC
%token IF THEN ELSE


%token TINT
%token TBOOL
%token TFLOAT
%token TUNIT
%token SEMICOLON

%left IN
%left SEMICOLON
%left ELSE
%nonassoc NOT PRINTINT 
%nonassoc EQ NEQ GREAT GREATEQ LESS LESSEQ
%left LOR
%left LAND
%left PLUS MINUS 
%left MULT DIV
%left PLUSPT MINUSPT
%left MULTPT DIVPT


%start prog
%type <Syntax.programme> prog


%%

prog: list_implem_decl; EOF  { $1 }; 

ty:
  | TBOOL        { TBool }
  | TINT         { TInt }
  | TFLOAT       { TFloat }
  | TUNIT        { TUnit }

fun_decl:
  | LET VAR LPAR list_typed_ident RPAR COLON ty EQ expr
    { {id = $2 ; var_list = $4 ; typ_retour = $7; corps = $9; isrec = true} }
  | LETREC VAR LPAR list_typed_ident RPAR COLON ty EQ expr IN expr
    { {id = $2; var_list = $4; typ_retour = $7; corps = $9; isrec = true} }


list_implem_decl:
  |  { [] }
  | list_implem_decl fun_decl {$2::$1}


expr:
  | VAR             { Var $1 }
  | INT             { Int $1 }
  | FLOAT           { Float $1 }
  | UNIT            { Unit  }
  | TRUE            { Bool true }
  | FALSE           { Bool false } 
  | LPAR expr RPAR   { $2 }
  | app_expr { $1 }
  | IF expr THEN expr ELSE expr        { If ($2, $4, $6) }
  | LET LPAR VAR COLON ty RPAR EQ expr IN expr
    { Let ($3, $5, $8, $10) }
  | expr PLUS expr     { BinaryOp (Plus, $1, $3) }
  | expr MINUS expr    { BinaryOp (Minus, $1, $3) }
  | expr MULT expr     { BinaryOp (Mult, $1, $3) }
  | expr DIV expr      { BinaryOp (Div, $1, $3) }
  | expr PLUSPT expr   { BinaryOp (PlusPT, $1, $3) }
  | expr MINUSPT expr  { BinaryOp (MinusPT, $1, $3) }
  | expr MULTPT expr   { BinaryOp (MultPT, $1, $3) }
  | expr DIVPT expr    { BinaryOp (DivPT, $1, $3) }
  | NOT expr          { UnaryOp (Not, $2) }
  | expr LAND expr     { BinaryOp (And, $1, $3) }
  | expr LOR expr      { BinaryOp (Or, $1, $3) }
  | expr EQ expr      { BinaryOp (Equal, $1, $3) }
  | expr NEQ expr     { BinaryOp (NEqual, $1, $3) }
  | expr GREAT expr    { BinaryOp (Great, $1, $3) }
  | expr GREATEQ expr  { BinaryOp (GreatEq, $1, $3) }
  | expr LESS expr    { BinaryOp (Less, $1, $3) }
  | expr LESSEQ expr  { BinaryOp (LessEq, $1, $3) }
  | expr SEMICOLON expr { Seq ($1, $3) }
  | PRINTINT  expr   { PrintInt $2 }

app_expr:
  | VAR LPAR list_expr RPAR { App ($1, $3) }

typed_ident:
  | VAR COLON ty { ($1,$3) }

list_expr :
  |  { [] }
  | expr { [$1] }
  | expr COMMA list_expr {$1::$3}

list_typed_ident :
  |  { [] }
  | typed_ident { [$1] }
  | typed_ident COMMA list_typed_ident   {$1::$3}

%%
