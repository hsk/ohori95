%{ open Tmss %}
%token <string> X %token <int> INT
%token TRUE FALSE CASE OF MODIFY LET IN EOF
%token SHARP LAMBDA DOT COMMA EQ LT GT LPAREN RPAREN LBRACE RBRACE
%token ARROW DARROW COLON DCOLON ALL U NOT POLY BOOL TINT IDX
%type <Tmss.k> k %start k
%type <Tmss.q> q %start q
%type <Tmss.m> m %start m
%%
k       : U                                     { U }
        | LBRACE LBRACE lqs RBRACE RBRACE       { KRecord($3) }
        | LT LT lqs GT GT                       { KVariant($3) }

q       : q1 ARROW q                            { TArr($1,$3) }
        | q1                                    { $1 }
q1      : TINT                                  { TInt }
        | BOOL                                  { TBool }
        | X                                     { Tx($1) }
        | LBRACE lqs RBRACE                     { TRecord($2) }
        | LT lqs GT                             { TVariant($2) }
        | ALL X DCOLON k DOT q                  { TAll($2,$4,$6) }
        | IDX LPAREN X COMMA q RPAREN DARROW q  { TIdx($3,$5,$8) }
        | LPAREN q RPAREN                       { $2 }
lqs     : X COLON q                             { [($1,$3)] }
        | X COLON q COMMA lqs                   { ($1,$3)::$5 }

m       : m m1                                  { MApp($1,$2) }
        | m1                                    { $1 }
m1      : m1 COLON q SHARP X                    { MDot($1,$3,$5) }
        | m2                                    { $1 }
m2      : m3 notqs                              { MTApp($1,$2) }
        | m3                                    { $1 }
m3      : X                                     { Mx($1) }
        | TRUE                                  { MTrue }
        | FALSE                                 { MFalse }
        | INT                                   { MInt($1) }
        | LAMBDA X COLON q DOT m                { MAbs($2,$4,$6) }
        | LBRACE lms RBRACE                     { MRecord($2) }
        | LT X EQ m GT COLON q                  { MVariant($2,$4,$7) }
        | CASE m OF LT lms GT                   { MCase($2,$5) }
        | MODIFY LPAREN m2 COLON q COMMA X COMMA m RPAREN
                                                { MModify($3,$5,$7,$9) }
        | POLY LPAREN m2 COLON q RPAREN         { MPoly($3,$5) }
        | LET X COLON q EQ m IN m               { MLet($2,$4,$6,$8) }
        | LPAREN m RPAREN                       { $2 }
lms     : X EQ m                                { [($1,$3)] }
        | X EQ m COMMA lms                      { ($1,$3)::$5 }
notqs   : NOT q                                 { [$2] }
        | NOT q notqs                           { $2::$3 }
