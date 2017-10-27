% ML-Style System λlet,#
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆,±]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,▷,⊢,⟹*,⟶,⟶*]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
term_expansion(A--B,B:-A).

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

% Kinding rules

K ⊢     T :: LQs  :- member(T::LQ2s,K), intersection(LQ2s,LQs,LQs).
_ ⊢  LQ2s :: LQs  :- intersection(LQ2s,LQs,LQs).
K ⊢     T ::{LQs} :- member(T::{LQ2s},K), intersection(LQ2s,LQs,LQs).
_ ⊢ {LQ2s}::{LQs} :- intersection(LQ2s,LQs,LQs).
_ ⊢     _ :: u.

% Substitutions

tsub(S,M,M_) :- foldl(tsub1(S),S,M,M_),!.
tsub1(S,N/X,X,N_) :- tsub(S,N,N_).
tsub1(_,_/_,X1,X1) :- t(X1).
tsub1(_,_/_,B,B) :- b(B).
tsub1(S,N/X,(Q1->Q2),(Q1_->Q2_)) :- tsub1(S,N/X,Q1,Q1_),tsub1(S,N/X,Q2,Q2_).
tsub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L:M,L:M_]>>tsub1(S,N/X,M,M_),LMs,LMs_).
tsub1(S,N/X,{LMs},{LMs_}) :- maplist({S,N,X}/[L:M,L:M_]>>tsub1(S,N/X,M,M_),LMs,LMs_).
tsub1(_,_/X,∀(X,K,Q),∀(X,K,Q)).
tsub1(S,N/X,∀(T,K,Q),∀(T,K_,Q_)) :- ksub1(S,N/X,K,K_),tsub1(S,N/X,Q,Q_).

ksub(S,M,M_) :- foldl(ksub1(S),S,M,M_),!.
ksub1(_,_/_,u,u).
ksub1(S,N/X,LQs,LQs_) :- maplist({S,N,X}/[L:Q,L:Q_]>>tsub1(S,N/X,Q,Q_), LQs,LQs_).
ksub1(S,N/X,{LQs},{LQs_}) :- maplist({S,N,X}/[L:Q,L:Q_]>>tsub1(S,N/X,Q,Q_), LQs,LQs_).

msub(S,M,M_) :- foldl(msub1(S),S,M,M_),!.
msub1(S,N/X,X,N_) :- msub(S,N,N_).
msub1(_,_/_,X1,X1) :- x(X1).
msub1(_,_/_,CB,CB) :- cb(CB).
msub1(_,_/X,λ(X,M),λ(X,M)).
msub1(S,N/X,λ(X1,M),λ(X1,M_)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,(M1$M2),(M1_$M2_)) :- msub1(S,N/X,M1,M1_), msub1(S,N/X,M2,M2_).
msub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>msub1(S,N/X,M,M_),LMs,LMs_).
msub1(S,N/X,(M#L),(M_#L)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,modify(M1,L,M2),modify(M1_,L,M2_)) :- msub1(S,N/X,M1,M1_), msub1(S,N/X,M2,M2_).
msub1(S,N/X,{[L=M]},{[L=M_]}) :- msub1(S,N/X,M,M_).
msub1(S,N/X,case(M,{LMs}),case(M_,{LMs_})) :- msub1(S,N/X,M,M_),maplist({S,N,X}/[L=Mi,L=Mi_]>>msub1(S,N/X,Mi,Mi_),LMs,LMs_).

mtsub(S,M,M_) :- foldl(mtsub1(S),S,M,M_),!.
mtsub1(S,N/X,X,N_) :- mtsub(S,N,N_).
mtsub1(S,N/X,λ(X1,M),λ(X1,M_)) :- tsub1(S,N/X,M,M_).
mtsub1(S,N/X,(M1$M2),(M1_$M2_)) :- mtsub1(S,N/X,M1,M1_), mtsub1(S,N/X,M2,M2_).
mtsub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>mtsub1(S,N/X,M,M_),LMs,LMs_).
mtsub1(S,N/X,(M#L),(M_#L)) :- mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,modify(M1,L,M2),modify(M1_,L,M2_)) :- mtsub1(S,N/X,M1,M1_), mtsub1(S,N/X,M2,M2_).
mtsub1(S,N/X,{[L=M]}:Q,{[L=M_]}:Q) :- mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,case(M,{LMs}),case(M_,{LMs_})) :- mtsub1(S,N/X,M,M_),maplist({S,N,X}/[L=Mi,L=Mi_]>>mtsub1(S,N/X,Mi,Mi_),LMs,LMs_).
mtsub1(_,_/_,M,M).

% Reduction rules

v    ::= cb | λ(x,e) | record(l=v) | {[l=v]}.

ev(H,(V1$E2),(V1$E2_)) :- v(V1),!,ev(H,E2,E2_).
ev(H,(E1$E2),(E1_$E2)) :- !,ev(H,E1,E1_).
ev(H,(let(X=E1); E2),(let(X=E1_); E2)) :- !,ev(H,E1,E1_).
ev(H,[L=V|LEs],[L=V|LEs_]) :- v(V),!,ev(H,LEs,LEs_).
ev(H,[L=E|LEs],[L=E_|LEs]) :- !,ev(H,E,E_).
ev(H,(E#L),(E_#L)) :- !,ev(H,E,E_).
ev(H,modify(V1,L,E2),modify(V1,L,E2_)) :- v(V1),!,ev(H,E2,E2_).
ev(H,modify(E1,L,E2),modify(E1_,L,E2)) :- !,ev(H,E1,E1_).
ev(H,{[L=E]},{[L=E_]}) :- !,ev(H,E,E_).
ev(H,case(E,{LEs}),case(E_,{LEs})) :- !,ev(H,E,E_).
ev(H/E,E,H) :- !.

ev(λ(X,E)$V)                ⟶ ev(E_)          :- msub([V/X],E,E_).
ev(LVs#Li)                  ⟶ ev(Vi)          :- member(Li=Vi,LVs).
ev(modify([Li=_ |LS],Li,N)) ⟶ ev([Li=N|LS]).
ev(modify([Li=Mi|LS],L,N))  ⟶ ev([Li=Mi|LS_]) :- ev(modify(LS,L,N)) ⟶ ev(LS_).
ev(case({[Li=V]},{Ls}))     ⟶ ev(Ei $ V)      :- member(Li=Ei,Ls).
ev(let(X = V); E)           ⟶ ev(E_)          :- msub([V/X],E,E_).

M ⟹ M_ :- ev(H/R,M,M_), ev(R) ⟶ ev(H).
M ⟹* M_ :- M ⟹ M1,!, M1 ⟹* M_.
M ⟹* M.

% Free Type variables

ftv(X,[X]) :- x(X).
ftv(B,[]) :- b(B).
ftv((Q1->Q2),FTV) :- ftv(Q1,FTV1),ftv(Q2,FTV2),union(FTV1,FTV2,FTV).
ftv(LMs,FTVs) :- foldl([_=M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LMs,[],FTVs).
ftv({LMs},{FTVs}) :- foldl([_=M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LMs,[],FTVs).
ftv(∀(T,K,Q),FTV) :- kftv(K,KFTV),ftv(Q,QFTV),union(KFTV,QFTV,FTV1),subtract(FTV1,T,FTV).

kftv(u,[]).
kftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
kftv({LQs},FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
tftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).

% Type system
reset :- bb_put(i,0).
fresh(T) :- bb_get(i,I), format(atom(T),'%x~w',[I]), I1 is I + 1, bb_put(i,I1).

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si::K|Ks_],[Si/T_|S_])) :-
  fresh(Si),foldxq(((X$Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

:- begin_var_names(['^[τt]'],['^(true|bool|int)$']).

u(K,E,(K0,S)) :- u(E,K,[],[],(_, K0, S, _)).
u(E,K,S,SK,(E_,K_,S_,SK_)) :- (E,K,S,SK) ⟹ (E_,K_,S_,SK_).
u(E,K,S,SK,(E,K,S,SK)).

% 3.4 Kinded Unification

F1 ⊆ F2 :- intersection(F2,F1,F1_),length(F1,L),length(F1_,L).
F1 ± F2 ⟹ F :-
  dom(F1,Dom1),dom(F2,Dom2),union(Dom1,Dom2,Dom),
  maplist([l,t]>>(member(l:t,F1);member(l:t,F2)),Dom,F).
  
dom(F,Dom) :- maplist([L:_,L]>>!,F,Dom).
% todo ftv

%(i)
([(τ,τ)|E],K,S,SK) ⟹ (E,K,S,SK).
%(ii)
([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_) :-
  t(t), ftv(τ,FTV), \+member(t,FTV),
  member((t,u),K0), subtract(K0,[(t,u)],K),
  esub([τ/t],E,E_), ksub([τ/t],K,K_),
  ssub([τ/t],S,S1), union(S1,[(t,τ)],S_),
  ssub([τ/t],SK,SK1), union(SK_,[(t,u)],SK_).
%(iii)
([(t1,t2)|E],K0,S,SK) ⟹ (E_, K_, S_,SK_) :-
  t(t1),t(t2),
  member((t1,F1),K0), record(F1), member((t2,F2),K0), record(F2), subtract(K0,[(t1,F1),(t2,F2)],K),
  dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom12,ED),
  union(E,ED,E1), esub([t2/t1],E1,E_),
  ksub([t2/t1],K,K1),F1 ± F2 ⟹ F12,tsub([t2/t1],F12,F12_),union(K1,[(t2,F12_)],K_),
  ssub([t2/t1],S,S1), union(S1,[(t1,t2)],S_),
  ssub([t2/t1],SK,SK1), union(SK1,[(t1,F1)],SK_).
%(iv)
([(t1,F2)|E],K0,S,SK) ⟹ (E_,K_, S_,SK_) :- record(F2),
  member((t1,F1),K0), record(F1), subtract(K0,[(t1,F1)],K),
  dom(F1,Dom1), dom(F2,Dom2), Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t, FTV),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom1,ED),
  union(E,ED,E1), esub([F2/t1],E1,E_),
  ksub([F2/t1],K,K_),
  ssub([F2/t1],S,S1), union(S1,[(t1,F2)],S_),
  ssub([F2/t1],SK,SK1), union(SK1,[(t1,F1)],SK_).
%(v)
([(F1,F2)|E],K,S,SK) ⟹ (E_,K,S,SK) :- record(F1),record(F2),
  dom(F1,Dom1), dom(F2,Dom2), Dom1=Dom2,
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom1,ED),
  union(E,ED,E_).
%(vi)
([(t1,t2)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_) :-
  member((t1,{F1}),K0),list(F1), member((t2,{F2}),K0),list(F2), subtract(K0,[(t1,{F1}),(t2,{F2})],K),
  dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom12,ED),
  union(E,ED,E1), esub([t2/t1],E1,E_),
  ksub([t2/t1],K,K1), F1 ± F2 ⟹ F12, tsub([t2/t1],{F12},{F12_}), union(K1,[(t2,{F12_})],K_),
  ssub([t2/t1],S,S1), union(S1,[(t1,t2)],S_),
  ssub([t2/t1],SK,SK1), union(SK1,[(t1,{F1})],SK_).
%(vii)
([(t1,{F2})|E],K0,S,SK) ⟹ (E_,K_,S_,SK_) :- list(F2),
  member((t1,{F1}),K0),list(F1), subtract(K0,[(t1,{F1})],K),
  dom(F1,Dom1), dom(F2,Dom2), Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t1, FTV),
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom1,ED),
  union(E,ED,E1), esub([{F2}/t1],E1,E_),
  ksub([{F2}/t1],K,K_),
  ssub([{F2}/t1],S,S1), union(S1,[(t1,{F2})],S_),
  ssub([{F2}/t1],SK,SK1), union(SK1,[(t1,{F1})],SK_).
% (viii)
([({F1},{F2})|E],K,S,SK) ⟹ (E_,K,S,SK) :- list(F1),list(F2),
  dom(F1,Dom1), dom(F2,Dom2), Dom1=Dom2,
  maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom1,ED),
  union(E, ED, E_).
%(ix)
([((τ11->τ21),(τ12->τ22))|E],K,S,SK) ⟹ (E_,K,S,SK) :-
  union(E,[(τ11,τ12),(τ21,τ22)],E_).

% 各ルールの左側にX∪Yという形式の表記がある場合、XとYは互いに素であると仮定します。

wk(K,T,x,(K_,[],x_,Sτ2)) :-
  member(x:Sτ, T),
  foldxq((x,Sτ,[],[]),(x_,Sτ1,SKs,S)),
  foldr({S}/[(Si::Ki),(Si::Ki_)]>>ksub(S,Ki,Ki_),SKs,K,K_),
  tsub(S,Sτ1,Sτ2).

wk(K,T,λ(x,E1), (K1,S1,λ(x:t_,M1),(t_->t1))) :-
  fresh(t), wk([t::u|K],[x:t|T],E1, (K1,S1,M1,t1)), tsub(S1,t,t_).

wk(K,T,(E1$E2),(K3,S321,(M1_ $ M2_),t3)) :-
  wk(K,T,E1,(K1,S1,M1,σ1)), subT(S1,T,T1),
  wk(K1,T1,E2,(K2,S2,M2,σ2)), tsub(S2,σ1,σ1_),
  fresh(t), u(K2,[(σ1_,(σ2->t))],(K3,S3)),
  union(S3,S2,S32), union(S32,S1,S321),
  msub(S32,M1,M1_), msub(S3,M2,M2_), tsub(S3,t,t3).

wk(K,T,[],(K,[],[],[])).
wk(K,T,[L1=E1|LEs],(Kn,S_,[L1=M1|LMs],[L1:τ1|LTs])) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),
  subT(S1,T,T1),
  wk(K1,T1,LEs,(Kn,S,LMs,LTs)),
  union(S1,S,S_).

wk(K,T,(E1#L),(K2,S,((M1_:t2_) # L),t1_)) :-
  wk(K,T,E1, (K1,S1,M1,τ1)),fresh(t1),fresh(t2),
  u([t1::u,t2::[l:t1]|K1],[(t2,τ1)],(K2,S2)),
  union(S2,S1,S), msub(S2,M1,M1_),
  tsub(S2,t1,t1_), tsub(S2,t2,t2_).

wk(K,T,modify(E1,L,E2),(K3,S321,modify(M1_:t2_,L,M2_),t2_)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),subT(S1,T,T1),
  wk(K1,T1,E2,(K2,S2,M2,τ2)),
  tsub(S2,τ1,τ1_),fresh(t1),fresh(t2),
  u([t1::u,t2::[l:t1]|K2],[(t1,τ2),(t2,τ1_)],(K3,S3)),
  union(S3,S2,S32),union(S32,S1,S321),
  msub(S32,M1,M1_),tsub(S3,t2,t2_),msub(S3,M2,M2_).

wk(K,T,case(E0,{Les}), (Kn1,S_, case(M0_,{LMs_}),t0_)) :-
  wk(K,T,E0,(K0,S0,M0,τ0)), subT(S0,T,T0), fresh(t0),
  foldr([Li=Ei,(Ki1,Ti1,LMs1,Lts1,K1,Tts1,S1),
    (Ki,Ti,[Li=Mi|LMs1],[Li:ti|Lts1],[ti::u|K1],[(τi,ti)|Tts1],S)]>>(
    wk(Ki1,Ti1,Ei,(Ki,Si,Mi,τi)), subT(Si,Ti1,Ti),
    union(Si,S1,S),fresh(ti)
  ),Les,(K0,T0,[],[],Kn,[],[]),(Kn,Tn,LMs,Lts,Kn_,Tts,S)),
  maplist({t0,S}/[(τi,ti),(τi_,(t0->ti))]>>tsub(S,τi,τi_),Tts,Tts_),
  tsub(S,τ0,τ0_), union([(τ0_,{Lts})],Tts_,Tts2),
  u(Kn_,Tts2, (Kn1,Sn1)),union(Sn1,S,S_),
  tsub(Sn1,t0,t0_),msub(S_,M0,M0_),
  maplist({S}/[Li=Mi,Li=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_).

wk(K,T,{[l=E1]},([t::{[l:τ1]}|K1],S1,({[l=M1]}:t),t)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),fresh(t).

wk(K,T,(let(X=E1);E2),(K2,S21,(let(X:σ1_=poly(M1_:σ1_)); M2),τ2)) :-
  wk(K,T,E1,(K1,S1,M1,τ1)),subT(S1,T,T1),
  cls(K1,T1,τ1,(K1_,σ1)),
  wk(K1_,[X:σ1|T1],E2,(K2,S2,M2,τ2)),
  tsub(S2,σ1,σ1_),msub(S2,M1,M1_),
  union(S2,S1,S21).

% todo subT
% todo cls
:- end_var_names(_).

:- halt.
