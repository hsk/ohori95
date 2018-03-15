{ open Mss_parser }
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
  | eof                  { EOF }
  | _ as i               { Printf.printf "error '%c'\n%!" i; failwith "lex error"  }
{ let parseE src = e token (Lexing.from_string src) }
