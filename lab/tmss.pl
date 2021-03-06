% Typed ML-Style System Λlet,#
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,⟹*,⟹,⟶,⟶*]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
:- set_prolog_flag(allow_variable_name_as_functor,true). % M(a) と書ける。
term_expansion(A--B,B:-A).

foldr(_,[],S,S) :- !. % 畳み込み
foldr(F,[X|Xs],S,S_) :- foldr(F,Xs,S,S1),!,call(F,X,S1,S_),!.

% Syntaxs

syntax(k).
syntax(t). t(T) :- atom(T), \+b(T). 
b ::= int | bool.
l ::= atom.
list(A) ::= [] | [A | list(A)].
record(A) ::= list(A).
variant(A) ::= {list(A)}.
q ::= b | t | (q->q) | record(l:q) | variant(l:q) | ∀(t,k,q).
k ::= u | record(l::q) | variant(l::q).

syntax(integer).
syntax(x). x(X) :- atom(X), \+cb(X).
i ::= integer.
cb ::= true | false | i.
/*e ::= x | cb | λ(x,e) | (e $ e) | (let(x=e);e)
    | record(l=e) | e#l | modify(e,l,e)
    | {[l=e]} | case(e,variant(l=e)). */
'M' ::= x!list(q) | cb | λ(x:q,'M') | ('M' $ 'M') | poly('M':q) | (let(x:q = 'M');'M')
    | record(l='M') | ('M':q) # l | modify('M':q,l,'M')
    | ({[l='M']}:q) | case('M',variant(l='M')).

v ::= cb | λ(x:q,'M') | record(l=v) | ({[l=v]}:q).

% Reduction rules

ev(H/R,(V1$E2),(V1$E2_)) :- v(V1),\+v(E2),!,ev(H/R,E2,E2_).
ev(H/R,(E1$E2),(E1_$E2)) :- \+v(E1),!,ev(H/R,E1,E1_).
ev(H/R,(let(X=E1); E2),(let(X=E1_); E2)) :- \+v(E1),!,ev(H/R,E1,E1_).
ev(H/R,[L=V|LEs],[L=V|LEs_]) :- v(V),!,ev(H/R,LEs,LEs_).
ev(H/R,[L=E|LEs],[L=E_|LEs]) :- \+v(E),!,ev(H/R,E,E_).
ev(H/R,(E#L),(E_#L)) :- \+v(E),!,ev(H/R,E,E_).
ev(H/R,modify(V1,L,E2),modify(V1,L,E2_)) :- v(V1),\+v(E2),!,ev(H/R,E2,E2_).
ev(H/R,modify(E1,L,E2),modify(E1_,L,E2)) :- \+v(E1),!,ev(H/R,E1,E1_).
ev(H/R,{[L=E]},{[L=E_]}) :- \+v(E),!,ev(H/R,E,E_).
ev(H/R,case(E,{LEs}),case(E_,{LEs})) :- \+v(E),!,ev(H/R,E,E_).
ev(H/E,E,H) :- !.

ev(λ(X:_,E)$V)              ⟶ ev(E_)          :- v(V),msub([V/X],E,E_).
ev(LVs#Li)                  ⟶ ev(Vi)          :- member(Li=Vi,LVs).
ev(modify([Li=_ |LS],Li,N)) ⟶ ev([Li=N|LS]).
ev(modify([Li=Ei|LS],L,N))  ⟶ ev([Li=Ei|LS_]) :- ev(modify(LS,L,N)) ⟶ ev(LS_).
ev(case({[Li=V]},{Ls}))     ⟶ ev(Ei $ V)      :- member(Li=Ei,Ls).
ev(let(X = V); E)           ⟶ ev(E_)          :- msub([V/X],E,E_).

ev(E) ⟹ ev(E_) :- ev(H/R,E,E_), ev(R) ⟶ ev(H).
ev(E) ⟹ ev(E_) :- ev(E) ⟶ ev(E_).
E ⟹* E_ :- ev(E) ⟹ ev(E1),!, E1 ⟹* E_.
E ⟹* E.

% Substitutions

tsub(S,X,N_) :- t(X),member(N/X,S),tsub(S,N,N_).
tsub(_,X1,X1) :- t(X1).
tsub(_,B,B) :- b(B).
tsub(S,(Q1->Q2),(Q1_->Q2_)) :- tsub(S,Q1,Q1_),tsub(S,Q2,Q2_).
tsub(S,LMs,LMs_) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,{LMs},{LMs_}) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,∀(T,K,Q),∀(T,K_,Q_)) :- subtract(S,[_/T],S_),ksub(S_,K,K_),tsub(S_,Q,Q_).

ksub(_,u,u).
ksub(S,LQs,LQs_) :- maplist({S}/[L::Q,L::Q_]>>tsub(S,Q,Q_), LQs,LQs_).
ksub(S,{LQs},{LQs_}) :- maplist({S}/[L::Q,L::Q_]>>tsub(S,Q,Q_), LQs,LQs_).

msub(S,X,N_) :- x(X),member(N/X,S),msub(S,N,N_).
msub(_,X,X) :- x(X).
msub(S,x(X,T),x(X_,T)) :- msub(S,X,X_).
msub(S,X!Ls,X_!Ls_) :- msub(S,X,X_),msub(S,Ls,Ls_),!.
msub(_,CB,CB) :- cb(CB).
msub(S,λ(X:Q,M),λ(X:Q,M_)) :- subtract(S,[_/X],S_),msub(S_,M,M_).
msub(S,(M1$M2),(M1_$M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,(M!Q),(M_!Q)) :- msub(S,M,M_).
msub(S,λ(T::K,M),λ(T::K,M_)) :- msub(S,M,M_).
msub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>msub(S,M,M_),LMs,LMs_).
msub(S,(M#L),(M_#L)) :- msub(S,M,M_).
msub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,{[L=M]}:Q,{[L=M_]}:Q) :- msub(S,M,M_).
msub(S,case(M,{LMs}),case(M_,{LMs_})) :- msub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_).

mtsub(S,X,N_) :- x(X),member(N/X,S),mtsub(S,N,N_).
mtsub(S,x(X,T),x(X_,T_)) :- tsub(S,T,T_),mtsub(S,X,X_).
mtsub(S,λ(X1:Q,M),λ(X1:Q_,M_)) :- tsub(S,Q,Q_),mtsub(S,M,M_).
mtsub(S,(M1$M2),(M1_$M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,(M!Q),(M_!Q_)) :- mtsub(S,M,M_), tsub(S,Q,Q_).
mtsub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>mtsub(S,M,M_),LMs,LMs_).
mtsub(S,(M#L),(M_#L)) :- mtsub(S,M,M_).
mtsub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,{[L=M]}:Q,{[L=M_]}:Q_) :- mtsub(S,M,M_),tsub(S,Q,Q_).
mtsub(S,case(M,{LMs}),case(M_,{LMs_})) :- mtsub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>mtsub(S,Mi,Mi_),LMs,LMs_).
mtsub(_,M,M).

/*
etsub(S,X,N_) :- member(N/X,S),!,etsub(S,N,N_).
etsub(S,X,X) :- x(X),!.
etsub(S,λ(X1,M),λ(X1,M_)) :- tsub(S,M,M_).
etsub(S,(M1$M2),(M1_$M2_)) :- etsub(S,M1,M1_), etsub(S,M2,M2_).
etsub(S,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>etsub(S,M,M_),LMs,LMs_).
etsub(S,(M#L),(M_#L)) :- etsub(S,M,M_).
etsub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- etsub(S,M1,M1_), etsub(S,M2,M2_).
etsub(S,{[L=M]}:Q,{[L=M_]}:Q) :- etsub(S,M,M_).
etsub(S,case(M,{LMs}),case(M_,{LMs_})) :- etsub(S,M,M_),maplist({S,N,X}/[L=Mi,L=Mi_]>>etsub(S,Mi,Mi_),LMs,LMs_).
*/
subE(S,E,E_) :- maplist(subE1(S),E,E_).
subE1(S,(T1,T2),(T1_,T2_)) :- tsub(S,T1,T1_),tsub(S,T2,T2_).
subT(S,T,T_) :- maplist(subT1(S),T,T_).
subT1(S,(X:T2),(X:T2_)) :- tsub(S,T2,T2_).
ssub(S,S1,S1_) :- maplist(ssub1(S),S1,S1_).
ssub1(S,T1/T2,T1_/T2_) :- tsub(S,T1,T1_),tsub(S,T2,T2_).


% Free Type variables
:- begin_var_names(['^[τtxσk]'],['^(true|bool|int)$']).

ftv(B,[]) :- b(B),!.
ftv(X,[X]) :- x(X).
ftv((Q1->Q2),FTV) :- ftv(Q1,FTV1),ftv(Q2,FTV2),union(FTV1,FTV2,FTV).
ftv(LTs,FTVs) :- foldl([_:T,FTV,FTV_]>>(ftv(T,FTVi),union(FTV,FTVi,FTV_)),LTs,[],FTVs).
ftv({LTs},{FTVs}) :- foldl([_:T,FTV,FTV_]>>(ftv(T,FTVi),union(FTV,FTVi,FTV_)),LTs,[],FTVs).
ftv(∀(T,K,Q),FTV) :- kftv(K,KFTV),ftv(Q,QFTV),union(KFTV,QFTV,FTV1),subtract(FTV1,T,FTV).

kftv(u,[]).
kftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
kftv({LQs},FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
tftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).

eftv(K,σ,EFTV) :- ftv(σ,FTV),member(σ::k,K),kftv(k,FTV2),union(FTV,FTV2,EFTV).
eftv(_,σ,FTV) :- ftv(σ,FTV).

% Type system
reset :- bb_put(i,0).
fresh(T) :- bb_get(i,I), format(atom(T),'%x~w',[I]), I1 is I + 1, bb_put(i,I1).

% 3.4 Kinded Unification

F1 ⊆ F2 :- intersection(F2,F1,F1_),length(F1,L),length(F1_,L).
±(F1, F2, F) :-
  dom(F1,Dom1),dom(F2,Dom2),union(Dom1,Dom2,Dom),
  maplist([L,t]>>(member(L:t,F1);member(L:t,F2)),Dom,F).

dom(F,Dom) :- maplist([L:_,L]>>!,F,Dom).

u(K,E,(K0,S)) :- u(E,K,[],[],(_, K0, S, _)).
u([],K,S,SK,([],K,S,SK)) /*:- writeln(b:u([],K,S,SK))*/.
u(E,K,S,SK,(E_,K_,S_,SK_)) :-
  u((E,K,S,SK) ⟹ (E1,K1,S1,SK1)),!,
  u(E1,K1,S1,SK1,(E_,K_,S_,SK_)).
u([(T1,T2)|E],K,S,SK,(E_,K_,S_,SK_)) :-
  u(([(T2,T1)|E],K,S,SK) ⟹ (E1,K1,S1,SK1)),!,
  u(E1,K1,S1,SK1,(E_,K_,S_,SK_)).

%u((E,K,S,SK) ⟹ _) :- writeln(a:u(E,K,S,SK)),fail.
%(i) type
u(([(τ,τ)|E],K,S,SK) ⟹ (E,K,S,SK)).
%(ii) 
u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  t(t), ftv(τ,FTV), \+member(t,FTV),
  member(t::u,K0), subtract(K0,[t::u],K),!,
  subE([τ/t],E,E_), ksub([τ/t],K,K_),
  ssub([τ/t],S,S1), union(S1,[τ/t],S_),
  ssub([τ/t],SK,SK1), union(SK1,[u/t],SK_).
u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  t(t), ftv(τ,FTV), \+member(t,FTV), \+member(t::_,K0),
  u(([(t,τ)|E],[t::u|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
u(([(∀(t,k,t1),τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  u(([(t1,τ)|E],[t::k|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
%(iii) record
u(([(t1,t2)|E],K0,S,SK) ⟹ (E_, K_, S_,SK_)) :-
  t(t1),t(t2),
  member(t1::F1,K0), record(l:q,F1), member((t2,F2),K0), record(l:q,F2), subtract(K0,[(t1,F1),(t2,F2)],K),
  dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom12,ED),
  union(E,ED,E1), subE([t2/t1],E1,E_),
  ksub([t2/t1],K,K1),'±'(F1, F2, F12),tsub([t2/t1],F12,F12_),union(K1,[(t2,F12_)],K_),
  ssub([t2/t1],S,S1), union(S1,[t2/t1],S_),
  ssub([t2/t1],SK,SK1), union(SK1,[F1/t1],SK_).
%(iv) record2
u(([(t1,F2)|E],K0,S,SK) ⟹ (E_,K_, S_,SK_)) :- record(l:q,F2),
  member(t1::F1,K0), record(l:q,F1), subtract(K0,[t1::F1],K),
  dom(F1,Dom1), dom(F2,Dom2),Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t, FTV),
  maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
  union(E,ED,E1), subE([F2/t1],E1,E_),
  ksub([F2/t1],K,K_),
  ssub([F2/t1],S,S1), union(S1,[F2/t1],S_),
  ssub([F2/t1],SK,SK1), union(SK1,[F1/t1],SK_).
%(v) record3
u(([(F1,F2)|E],K,S,SK) ⟹ (E_,K,S,SK)) :- record(l:q,F1),record(l:q,F2),
  dom(F1,Dom1), dom(F2,Dom2), Dom1=Dom2,
  maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
  union(E,ED,E_).
%(vi) variant
u(([(t1,t2)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  t(t1),t(t2),
  member((t1,{F1}),K0),list(l:q,F1), member((t2,{F2}),K0),list(l:q,F2), subtract(K0,[(t1,{F1}),(t2,{F2})],K),
  dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
  maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom12,ED),
  union(E,ED,E1), subE([t2/t1],E1,E_),
  ksub([t2/t1],K,K1), ±(F1,F2, F12), tsub([t2/t1],{F12},{F12_}), union(K1,[(t2,{F12_})],K_),
  ssub([t2/t1],S,S1), union(S1,[t2/t1],S_),
  ssub([t2/t1],SK,SK1), union(SK1,[{F1}/t1],SK_).
%(vii) variant2
u(([(t1,{F2})|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :- t(t1), list(l:q,F2),
  member((t1::{F1}),K0),list(l:q,F1), subtract(K0,[(t1::{F1})],K),
  dom(F1,Dom1), dom(F2,Dom2), Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t1, FTV),
  maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
  union(E,ED,E1), subE([{F2}/t1],E1,E_),
  ksub([{F2}/t1],K,K_),
  ssub([{F2}/t1],S,S1), union(S1,[{F2}/t1],S_),
  ssub([{F2}/t1],SK,SK1), union(SK1,[{F1}/t1],SK_).
% (viii) variant3
u(([({F1},{F2})|E],K,S,SK) ⟹ (E_,K,S,SK)) :- list(l:q,F1),list(l:q,F2),
  dom(F1,Dom), dom(F2,Dom),
  maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom,ED),
  union(E, ED, E_).
%(ix) arr
u(([((τ11->τ21),(τ12->τ22))|E],K,S,SK) ⟹ (E_,K,S,SK)) :-
  union(E,[(τ11,τ12),(τ21,τ22)],E_).

% alorighm WK

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si::K|Ks_],[Si/T_|S_])) :-
  fresh(Si),!,foldxq((x(X,Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

cls(K, _, ∀(t,k,τ), (K,∀(t,k,τ))).
cls(K, T, τ, (K0,τ_)) :-
  eftv(K, τ,τFTV), eftv(K, T, TFTV), subtract(τFTV, TFTV, ts),
  findall((Ti::Ki),(member(Ti::Ki,K),member(Ti,ts)),K1),
  subtract(K,K1,K0),foldr([Ti::Ki,τi,∀(Ti,Ki,τi)]>>!,K1,τ,τ_).


:- end_var_names(_).
:- end_var_names(_).
