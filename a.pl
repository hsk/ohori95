:- _a=1,writeln(_a).
:- __σ=1,writeln(__σ).
:- _t=1,writeln(_t).

t(Sτ):-writeln(Sτ).

s(Aσ):-writeln(Aσ).

:- t(a).

varcnv(G,T,T_) :- atom(T),member(T:T_,G).
varcnv(G,T,T_) :- compound(T), T =..[N|L], maplist(varcnv(G),L,L_), T_ =..[N|L_].
varcnv(G,T,T).

term_expansion(T,T_) :- varcnv([τ1:_],T,T_),writeln(T_).


:- τ1=hogehoge7,writeln(τ1).

:- Aτ=1,
   Bτ=1,
   Cτ=1,
   Dτ=1,
   Eτ=1,
   Fτ=1,
   Gτ=1,
   Hτ=1,
   Iτ=1,
   Jτ=1,
   Kτ=1,
   Lτ=1,
   Mτ=1,
   Nτ=1,
   Oτ=1,
   Pτ=1,
   Qτ=1,
   Rτ=1,
   Sτ=1,
   Tτ=1,
   Uτ=1,
   Vτ=1,
   Wτ=1,
   Xτ=1,
   Yτ=1,
   Zτ=1.
:- A' = 1, writeln(A').

:- halt.
