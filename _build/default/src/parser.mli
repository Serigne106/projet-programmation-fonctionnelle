
(* The type of tokens. *)

type token = 
  | VAR of (Syntax.idvar)
  | UNIT of (unit)
  | TUNIT
  | TRUE
  | TINT
  | THEN
  | TFLOAT
  | TBOOL
  | SEMICOLON
  | RPAR
  | PLUSPT
  | PLUS
  | NOT
  | NEQ
  | MULTPT
  | MULT
  | MINUSPT
  | MINUS
  | LPAR
  | LOR
  | LET
  | LESSEQ
  | LESS
  | LAND
  | INT of (int)
  | IN
  | IF
  | GREATEQ
  | GREAT
  | FLOAT of (float)
  | FALSE
  | EQ
  | EOF
  | ELSE
  | DIVPT
  | DIV
  | COMMA
  | COLON

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.programme)
