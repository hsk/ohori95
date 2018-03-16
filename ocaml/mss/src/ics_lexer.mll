{ open Ics_parser }
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
let alphaNum = alpha | digit
rule token = parse
  | [' ' '\t' '\n' '\r'] { token lexbuf }
  | alpha alphaNum* as x { match x with
                           | "true"   -> TRUE   | "false" -> FALSE
                           | "switch" -> SWITCH | "of"    -> OF
                           | "modify" -> MODIFY | "Poly"  -> POLY
                           | "let"    -> LET    | "in"    -> IN    | x -> X x }
  | '-'? digit+ as i     { INT (int_of_string i) }
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
  | "["                  { LBRACK }
  | "]"                  { RBRACK }
  | eof                  { EOF }
  | _ as i               { Printf.printf "error '%c'\n%!" i; failwith "lex error"  }
{ let parseC src = c token (Lexing.from_string src) }
