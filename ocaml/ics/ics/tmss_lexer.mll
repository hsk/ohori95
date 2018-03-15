{
  open Tmss_parser
}
let lower = ['a'-'z']
let upper = ['A'-'Z']
let digit = ['0'-'9']
let alpha = lower | upper | '_' 
let alphaNum = alpha | digit
let atom     = alpha alphaNum*
rule token = parse
  | [' ' '\t' '\n' '\r'] { token lexbuf }
  | atom as x            { match x with
                           | "true"   -> TRUE
                           | "false"  -> FALSE
                           | "case"   -> CASE
                           | "of"     -> OF
                           | "modify" -> MODIFY
                           | "let"    -> LET
                           | "in"     -> IN
                           | "Poly"   -> POLY
                           | "int"    -> TINT
                           | "bool"   -> BOOL
                           | "idx"    -> IDX
                           | "U"      -> U
                           | x        -> X x }
  | '-'? digit+ as i     { INT (int_of_string i) }
  | "#"                  { SHARP }
  | "λ"                  { LAMBDA }
  | "."                  { DOT }
  | ","                  { COMMA }
  | "="                  { EQ }
  | "<"                  { LT }
  | ">"                  { GT }
  | "("                  { LPAREN }
  | ")"                  { RPAREN }
  | "{"                  { LBRACE }
  | "}"                  { RBRACE }
  | "->"                 { ARROW }
  | "=>"                 { DARROW }
  | "::"                 { DCOLON }
  | ":"                  { COLON }
  | "∀"                 { ALL }
  | "!"                  { NOT }
  | eof                  { EOF }
  | _                    { failwith "lex error" }
{
let parsek src = k token (Lexing.from_string src)
let parseq src = q token (Lexing.from_string src)
let parseM src = m token (Lexing.from_string src)
}
