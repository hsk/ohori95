%{ open Mss %}
%token <string> X %token <int> INT
%token TRUE FALSE CASE OF MODIFY LET IN EOF
%token SHARP LAMBDA DOT COMMA EQ LT GT LPAREN RPAREN LBRACE RBRACE
%type <Mss.e> e %start e
%%
l   : X                                       { $1 }
i   : INT                                     { EInt $1 }
cb  : TRUE                                    { ETrue }
    | FALSE                                   { EFalse }
    | i                                       { $1 }
exp : e EOF                                   { $1 }
e   : e e1                                    { EApp($1,$2) }
    | e1                                      { $1 }
e1  : e1 SHARP l                              { EDot($1,$3) }
    | e2                                      { $1 }
e2  : X                                       { Ex $1 }
    | cb                                      { $1 }
    | LAMBDA X DOT e                          { EAbs($2,$4) }
    | LBRACE les RBRACE                       { ERecord $2 }
    | LT l EQ e GT                            { EVariant($2,$4) }
    | CASE e OF LT les GT                     { ECase($2,$5) }
    | MODIFY LPAREN e COMMA l COMMA e RPAREN  { EModify($3,$5,$7) }
    | LET X EQ e IN e                         { ELet($2,$4,$6) }
    | LPAREN e RPAREN                         { $2 }
le  : l EQ e                                  { ($1,$3) }
les : le                                      { [$1] }
    | le COMMA les                            { $1::$3 }
