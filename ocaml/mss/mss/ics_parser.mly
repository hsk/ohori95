%{ open Ics %}
%token <string> X %token <int> INT
%token TRUE FALSE SWITCH OF MODIFY POLY LET IN EOF
%token LAMBDA DOT COMMA EQ LT GT LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%type <Ics.c> c %start c
%%
c   : c c1                                     { CApp($1,$2) }
    | c1                                       { $1 }
c1  : c1 LBRACK idx RBRACK                     { CDot($1,$3) }
    | c2                                       { $1 }
c2  : X                                        { Cx $1 }
    | TRUE                                     { CTrue }
    | FALSE                                    { CFalse }
    | INT                                      { CInt $1 }
    | LAMBDA X DOT c                           { CAbs($2,$4) }
    | LBRACE cs RBRACE                         { CRecord $2 }
    | LT idx EQ c GT                           { CVariant($2,$4) }
    | SWITCH c OF cs                           { CSwitch($2,$4) }
    | MODIFY LPAREN c COMMA idx COMMA c RPAREN { CModify($3,$5,$7) }
    | LET X EQ c IN c                          { CLet($2,$4,$6) }
    | LPAREN c RPAREN                          { $2 }
cs  : c                                        { [$1] }
    | c COMMA cs                               { $1::$3 }
idx : INT                                      { CInt $1 }
    | X                                        { Cx $1 }
