% ML-Style System λlet,#
:- op(600,xfx,[#]).
:- op(650,yfx,[$,!,⊆]).
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
k ::= u | record(l:q) | variant(l:q).

syntax(integer).
syntax(x). x(X) :- atom(X), \+cb(X).
i ::= integer.
cb ::= true | false | i.
e ::= x | cb | λ(x,e) | (e $ e) | (let(x=e);e)
    | record(l=e) | e#l | modify(e,l,e)
    | {[l=e]} | case(e,variant(l=e)).

v ::= cb | λ(x,e) | record(l=v) | {[l=v]}.

'M' ::= x | 'M'!q | cb | λ(x:q,'M') | ('M' $ 'M') | poly('M':q) | (let(x:q = 'M');'M')
    | record(l='M') | ('M':q) # l | modify('M':q,l,'M')
    | ({[l='M']}:q) | case('M',variant(l='M')).

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

ev(λ(X,E)$V)                ⟶ ev(E_)          :- v(V),esub([V/X],E,E_).
ev(LVs#Li)                  ⟶ ev(Vi)          :- member(Li=Vi,LVs).
ev(modify([Li=_ |LS],Li,N)) ⟶ ev([Li=N|LS]).
ev(modify([Li=Ei|LS],L,N))  ⟶ ev([Li=Ei|LS_]) :- ev(modify(LS,L,N)) ⟶ ev(LS_).
ev(case({[Li=V]},{Ls}))     ⟶ ev(Ei $ V)      :- member(Li=Ei,Ls).
ev(let(X = V); E)           ⟶ ev(E_)          :- esub([V/X],E,E_).

ev(E) ⟹ ev(E_) :- ev(H/R,E,E_), ev(R) ⟶ ev(H).
ev(E) ⟹ ev(E_) :- ev(E) ⟶ ev(E_).
E ⟹* E_ :- ev(E) ⟹ ev(E1),!, E1 ⟹* E_.
E ⟹* E.

% Substitutions
esub(S,X,N_) :- member(N/X,S),!,esub(S,N,N_).
esub(_,X,X) :- x(X),!.
esub(_,CB,CB) :- cb(CB),!.
esub(S,λ(X,M),λ(X,M_)) :- !,subtract(S,[_/X],S_),esub(S_,M,M_).
esub(S,(M1$M2),(M1_$M2_)) :- esub(S,M1,M1_), esub(S,M2,M2_).
esub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>esub(S,M,M_),LMs,LMs_).
esub(S,(M#L),(M_#L)) :- !,esub(S,M,M_).
esub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- esub(S,M1,M1_), esub(S,M2,M2_).
esub(S,{[L=M]},{[L=M_]}) :- esub(S,M,M_).
esub(S,case(M,{LMs}),case(M_,{LMs_})) :- esub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>esub(S,Mi,Mi_),LMs,LMs_).

tsub(S,X,N_) :- t(X),member(N/X,S),tsub(S,N,N_).
tsub(_,X1,X1) :- t(X1).
tsub(_,B,B) :- b(B).
tsub(S,(Q1->Q2),(Q1_->Q2_)) :- tsub(S,Q1,Q1_),tsub(S,Q2,Q2_).
tsub(S,LMs,LMs_) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,{LMs},{LMs_}) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,∀(T,K,Q),∀(T,K_,Q_)) :- subtract(S,[_/T],S_),ksub(S_,K,K_),tsub(S_,Q,Q_).

ksub(_,u,u).
ksub(S,LQs,LQs_) :- maplist({S}/[L:Q,L:Q_]>>tsub(S,Q,Q_), LQs,LQs_).
ksub(S,{LQs},{LQs_}) :- maplist({S}/[L:Q,L:Q_]>>tsub(S,Q,Q_), LQs,LQs_).

msub(S,X,N_) :- x(X),member(N/X,S),msub(S,N,N_).
msub(_,X,X) :- x(X).
msub(S,(X!T),(X_!T)) :- msub(S,X,X_).
msub(_,CB,CB) :- cb(CB).
msub(S,λ(X:Q,M),λ(X:Q,M_)) :- subtract(S,[_/X],S_),msub(S_,M,M_).
msub(S,(M1$M2),(M1_$M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,(M!Q),(M_!Q)) :- msub(S,M,M_).
msub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>msub(S,M,M_),LMs,LMs_).
msub(S,((M:T)#L),((M_:T)#L)) :- msub(S,M,M_).
msub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,{[L=M]}:Q,{[L=M_]}:Q) :- msub(S,M,M_).
msub(S,case(M,{LMs}),case(M_,{LMs_})) :- msub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_).

mtsub(S,X,N_) :- x(X),member(N/X,S),mtsub(S,N,N_).
mtsub(S,(X!T),(X_!T_)) :- tsub(S,T,T_),mtsub(S,X,X_).
mtsub(S,λ(X1:Q,M),λ(X1:Q_,M_)) :- tsub(S,Q,Q_),mtsub(S,M,M_).
mtsub(S,(M1$M2),(M1_$M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,(M!Q),(M_!Q_)) :- mtsub(S,M,M_), tsub(S,Q,Q_).
mtsub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>mtsub(S,M,M_),LMs,LMs_).
mtsub(S,((M:T)#L),((M_:T_)#L)) :- tsub(S,T,T_),mtsub(S,M,M_).
mtsub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,{[L=M]}:Q,{[L=M_]}:Q_) :- mtsub(S,M,M_),tsub(S,Q,Q_).
mtsub(S,case(M,{LMs}),case(M_,{LMs_})) :- mtsub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>mtsub(S,Mi,Mi_),LMs,LMs_).
mtsub(_,M,M).

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

eftv(K,σ,EFTV) :- ftv(σ,FTV),member(σ:k,K),kftv(k,FTV2),union(FTV,FTV2,EFTV).
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

u((E,K,S,SK) ⟹ _) :- writeln(a:u(E,K,S,SK)),fail.
%(i) type
u(([(τ,τ)|E],K,S,SK) ⟹ (E,K,S,SK)).
%(ii) 
u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  t(t), ftv(τ,FTV), \+member(t,FTV),
  member(t:u,K0), subtract(K0,[t:u],K),!,
  subE([τ/t],E,E_), ksub([τ/t],K,K_),
  ssub([τ/t],S,S1), union(S1,[τ/t],S_),
  ssub([τ/t],SK,SK1), union(SK1,[u/t],SK_).
u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  t(t), ftv(τ,FTV), \+member(t,FTV), \+member(t:_,K0),
  u(([(t,τ)|E],[t:u|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
u(([(∀(t,k,t1),τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
  u(([(t1,τ)|E],[t:k|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
%(iii) record
u(([(t1,t2)|E],K0,S,SK) ⟹ (E_, K_, S_,SK_)) :-
  t(t1),t(t2),
  member(t1:F1,K0), record(l:q,F1), member((t2,F2),K0), record(l:q,F2), subtract(K0,[(t1,F1),(t2,F2)],K),
  dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom12,ED),
  union(E,ED,E1), subE([t2/t1],E1,E_),
  ksub([t2/t1],K,K1),'±'(F1, F2, F12),tsub([t2/t1],F12,F12_),union(K1,[(t2,F12_)],K_),
  ssub([t2/t1],S,S1), union(S1,[t2/t1],S_),
  ssub([t2/t1],SK,SK1), union(SK1,[F1/t1],SK_).
%(iv) record2
u(([(t1,F2)|E],K0,S,SK) ⟹ (E_,K_, S_,SK_)) :- record(l:q,F2),
  member(t1:F1,K0), record(l:q,F1), subtract(K0,[t1:F1],K),
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
  member((t1:{F1}),K0),list(l:q,F1), subtract(K0,[(t1:{F1})],K),
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

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si:K|Ks_],[Si/T_|S_])) :-
  fresh(Si),!,foldxq(((X!Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

cls(K, _, ∀(t,k,τ), (K,∀(t,k,τ))).
cls(K, T, τ, (K0,τ_)) :-
  eftv(K, τ,τFTV), eftv(K, T, TFTV), subtract(τFTV, TFTV, ts),
  findall((Ti:Ki),(member(Ti:Ki,K),member(Ti,ts)),K1),
  subtract(K,K1,K0),foldr([Ti:Ki,τi,∀(Ti,Ki,τi)]>>!,K1,τ,τ_).

wk(K,_,I,(K,[],I,int)) :- i(I).
wk(K,_,true,(K,[],true,bool)) :- !.
wk(K,_,false,(K,[],false,bool)) :- !.
wk(K,T,x,(K_,[],x_,Sτ2)) :-
  x(x),
  member(x:Sτ, T),
  foldxq((x,Sτ,[],[]),(x_,Sτ1,SKs,S)),
  maplist({S}/[(Si:Ki),(Si:Ki_)]>>ksub(S,Ki,Ki_),SKs,SKs_),union(K,SKs_,K_),  tsub(S,Sτ1,Sτ2).
wk(K,T,λ(x,E1), (K1,S1,λ(x:t_,M1),(t_->t1))) :-
  fresh(t), wk([t:u|K],[x:t|T],E1, (K1,S1,M1,t1)), tsub(S1,t,t_).
wk(K,T,(E1$E2),(K3,S321,(M1_ $ M2_),t3)) :-
  wk(K,T,E1,(K1,S1,M1,σ1)), subT(S1,T,T1),
  wk(K1,T1,E2,(K2,S2,M2,σ2)), tsub(S2,σ1,σ1_),
  fresh(t),
  u(K2,[(σ1_,(σ2->t))],(K3,S3)),
  writeln(u(K2,[(σ1_,(σ2->t))],(K3,S3))),
  union(S3,S2,S32), union(S32,S1,S321),
  mtsub(S32,M1,M1_), mtsub(S3,M2,M2_), tsub(S3,t,t3).
wk(K,_,[],(K,[],[],[])).
wk(K,T,[L1=E1|LEs],(Kn,S_,[L1=M1|LMs],[L1:τ1|LTs])) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),
  subT(S1,T,T1),
  wk(K1,T1,LEs,(Kn,S,LMs,LTs)),
  union(S1,S,S_).
wk(K,T,(E1#L),(K2,S,((M1_:t2_) # L),t1_)) :-
  wk(K,T,E1, (K1,S1,M1,τ1)),fresh(t1),fresh(t2),
  u([t1:u,t2:[L:t1]|K1],[(t2,τ1)],(K2,S2)),
  union(S2,S1,S), msub(S,M1,M1_),
  tsub(S,t1,t1_), tsub(S,t2,t2_).
wk(K,T,modify(E1,L,E2),(K3,S321,modify(M1_:t2_,L,M2_),t2_)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),subT(S1,T,T1),
  wk(K1,T1,E2,(K2,S2,M2,τ2)),
  tsub(S2,τ1,τ1_),fresh(t1),fresh(t2),
  u([t1:u,t2:[L:t1]|K2],[(t1,τ2),(t2,τ1_)],(K3,S3)),
  union(S3,S2,S32),union(S32,S1,S321),
  msub(S32,M1,M1_),tsub(S3,t2,t2_),msub(S3,M2,M2_).
wk(K,T,case(E0,{Les}), (Kn1,S_, case(M0_,{LMs_}),t0_)) :-
  wk(K,T,E0,(K0,S0,M0,τ0)), subT(S0,T,T0), fresh(t0),
  foldr([Li=Ei,(Ki1,Ti1,LMs1,Lts1,K1,Tts1,S1),
    (Ki,Ti,[Li=Mi|LMs1],[Li:ti|Lts1],[ti:u|K1],[(τi,ti)|Tts1],S)]>>(
    wk(Ki1,Ti1,Ei,(Ki,Si,Mi,τi)), subT(Si,Ti1,Ti),
    union(Si,S1,S),fresh(ti)
  ),Les,(K0,T0,[],[],Kn,[],[]),(Kn,_,LMs,Lts,Kn_,Tts,S)),
  maplist({t0,S}/[(τi,ti),(τi_,(t0->ti))]>>tsub(S,τi,τi_),Tts,Tts_),
  tsub(S,τ0,τ0_), union([(τ0_,{Lts})],Tts_,Tts2),
  u(Kn_,Tts2, (Kn1,Sn1)),union(Sn1,S,S_),
  tsub(Sn1,t0,t0_),msub(S_,M0,M0_),
  maplist({S}/[Li=Mi,Li=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_).
wk(K,T,{[L=E1]},([t:{[L:τ1]}|K1],S1,({[L=M1]}:t),t)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),fresh(t).
wk(K,T,(let(X=E1);E2),(K2,S21,(let(X:σ1_=poly(M1_:σ1_)); M2),τ2)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),!,subT(S1,T,T1),
  cls(K1,T1,τ1,(K1_,σ1)),
  wk(K1_,[X:σ1|T1],E2,(K2,S2,M2,τ2)),!,
  tsub(S2,σ1,σ1_),msub(S2,M1,M1_),
  union(S2,S1,S21).

:- end_var_names(_).
