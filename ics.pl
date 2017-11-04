% implementation calculs system
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,⟹*,⟹,⟶,⟶*]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
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
q ::= b | t | (q->q) | record(l:q) | variant(l:q) | idx(l,q,q) | ∀(t,k,q).
k ::= u | record(l::q) | variant(l::q).

syntax(integer).
syntax(x). x(X) :- atom(X), \+cb(X).
i ::= integer.
cb ::= true | false | i.
e ::= x | cb | λ(x,e) | (e $ e) | (let(x=e);e)
    | record(l=e) | e#l | modify(e,l,e)
    | {[l=e]} | case(e,variant(l=e)).

syntax('I'). 'I'(I) :- integer(I).
'Ï' ::= 'I' | i.
'C' ::= x | cb |λ(x,'C') | ('C' $ 'C') | (let(x='C'); 'C') | record('C') | 'C'#['Ï']
    | modify('C','Ï','C') | {['Ï'='C']} | switch('C', record('C')) | λ('I','C') | ('C' $ 'Ï').

% Reduction rules

csub(S,X,N_) :- member(N/X,S),!,csub(S,N,N_).
csub(_,X,X) :- x(X),!.
csub(_,CB,CB) :- cb(CB),!.
csub(S,λ(X,C),λ(X,C_)) :- !,subtract(S,[_/X],S_),csub(S_,C,C_).
csub(S,(C1$C2),(C1_$C2_)) :- csub(S,C1,C1_), csub(S,C2,C2_).
csub(S,Cs,Cs_) :- maplist({S}/[C,C_]>>csub(S,C,C_),Cs,Cs_).
csub(S,(C#[I]),(C_#[I])) :- !,csub(S,C,C_).
csub(S,modify(C1,I,C2),modify(C1_,I,C2_)) :- csub(S,C1,C1_), csub(S,C2,C2_).
csub(S,{[I=C]},{[I=C_]}) :- csub(S,C,C_).
csub(S,switch(C,Cs),switch(C_,Cs_)) :- csub(S,C,C_),maplist({S}/[Ci,Ci_]>>csub(S,Ci,Ci_),Cs,Cs_).

v ::= cb | λ(x,'C') | record(v) | {['Ï'=v]} | λ('I','C'). % (for some C' such that C'↓C').%todo
/*
EV[] ::= [·] | EV[] C | V EV[] | let x=EV[] in C | {V,···,V,EV[],···} | EV[][Ï]
        | modify(EV[],I,C) | modify(V,Ï,EV[]) | <Ï=EV[]> | switch EV[] of C,···,C
        | EV[] Ï | λI.EV[]
*/
ev(H/R,(V1$C2),(V1$C2_)) :- v(V1),\+v(C2),!,ev(H/R,C2,C2_).
ev(H/R,(C1$C2),(C1_$C2)) :- \+v(C1),!,ev(H/R,C1,C1_).
ev(H/R,(let(X=C1); C2),(let(X=C1_); C2)) :- \+v(C1),!,ev(H/R,C1,C1_).
ev(H/R,[V|Cs],[V|Cs_]) :- v(V),!,ev(H/R,Cs,Cs_).
ev(H/R,[C|Cs],[C_|Cs]) :- \+v(C),!,ev(H/R,C,C_).
ev(H/R,(C#[Ï]),(C_#[Ï])) :- \+v(C),!,ev(H/R,C,C_).
ev(H/R,modify(V1,I,C2),modify(V1,I,C2_)) :- v(V1),\+v(C2),!,ev(H/R,C2,C2_).
ev(H/R,modify(C1,I,C2),modify(C1_,I,C2)) :- \+v(C1),!,ev(H/R,C1,C1_).
ev(H/R,{[Ï=C]},{[Ï=C_]}) :- \+v(C),!,ev(H/R,C,C_).
ev(H/R,switch(C,Cs),switch(C_,Cs)) :- \+v(C),!,ev(H/R,C,C_).
ev(H/E,E,H) :- !.
/*
EV[(λx.C) V]                                 ⟶ EV[[V/x]C]
EV[{V1,···,Vn}[i]]                           ⟶ EV[Vi]
EV[modify({V1,···,Vi−1,Vi,Vi+1,···,Vn},i,V)] ⟶ EV[{V1,···,Vi−1,V,Vi+1,···,Vn}]
EV[switch <i=V> of C1,···,Cn]                ⟶ EV[Ci V]
%EV[(λI.C) Ï]                                ⟶ EV[[Ï/I]C] if C↓C
EV[let x=V in C]                             ⟶ EV[[V/x]C]
*/

ev(λ(X,C)$V)                ⟶ ev(C_)          :- v(V),csub([V/X],C,C_).
ev(Vs#[I])                  ⟶ ev(Vi)          :- nth0(Vs,I,Vi).
ev(modify([_ |LS],0,N))     ⟶ ev([N|LS]).
ev(modify([Mi|LS],I,N))     ⟶ ev([Mi|LS_])    :- I_ is I - 1, ev(modify(LS,I_,N)) ⟶ ev(LS_).
ev(switch({[I=V]},Cs))      ⟶ ev(Ci $ V)      :- nth0(Cs,I,Ci).
ev(λ(I,C)$Ï)                ⟶ ev(C_)          :- 'Ï'(Ï),csub([Ï/I],C,C_).
ev(let(X = V); C)           ⟶ ev(C_)          :- csub([V/X],C,C_).

ev(C) ⟹ ev(C_) :- ev(H/R,C,C_), ev(R) ⟶ ev(H).
ev(C) ⟹ ev(C_) :- ev(C) ⟶ ev(C_).
C ⟹* C_ :- ev(C) ⟹ ev(C1),!, C1 ⟹* C_.
C ⟹* C.

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

/*

msub(S,X,N_) :- x(X),member(N/X,S),msub(S,N,N_).
msub(_,X,X) :- x(X).
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
mtsub(S,λ(X1:Q,M),λ(X1:Q_,M_)) :- tsub(S,Q,Q_),mtsub(S,M,M_).
mtsub(S,(M1$M2),(M1_$M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,(M!Q),(M_!Q_)) :- mtsub(S,M,M_), tsub(S,Q,Q_).
mtsub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>mtsub(S,M,M_),LMs,LMs_).
mtsub(S,(M#L),(M_#L)) :- mtsub(S,M,M_).
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
*/

:- begin_var_names(['^[τtxσk]'],['^(true|bool|int)$']).
/*
% Free Type variables

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

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si::K|Ks_],[Si/T_|S_])) :-
  fresh(Si),foldxq(((X$Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

cls(K, T, τ, (K0,τ_)) :-
  eftv(K, τ,τFTV), eftv(K, T, TFTV), subtract(τFTV, TFTV, ts),
  findall((Ti::Ki),(member(Ti::Ki,K),member(Ti,ts)),K1),
  subtract(K,K1,K0),foldr([Ti::Ki,τi,∀(Ti,Ki,τi)]>>!,K1,τ,τ_).

% 3.4 Kinded Unification

F1 ⊆ F2 :- intersection(F2,F1,F1_),length(F1,L),length(F1_,L).
±(F1, F2, F) :-
  dom(F1,Dom1),dom(F2,Dom2),union(Dom1,Dom2,Dom),
  maplist([L,t]>>(member(L:t,F1);member(L:t,F2)),Dom,F).

dom(F,Dom) :- maplist([L:_,L]>>!,F,Dom).


*/

idxSet(t::u,[]).
idxSet(t::F,Is) :- maplist([L:_,I]>>idx(L,t,I),F,Is).
idxSet(t::{F},Is) :- maplist([L:_,I]>>idx(L,t,I),F,Is).
idxSet(∀(t,k,τ),Is) :- idSet(t::k,Is1),idxSet(τ,Is2),union(Is1,Is2,Is).
idxSet(K,Is) :- foldl([t::k,Is1,Is3]>>(idxSet(t::k,Is2),union(Is1,Is2,Is3)),K,[],Is).

c(L,T,x(x,τ1), x(x,Ï1)) :- ∀(t1,k1,idx(l1,t1_) ⇒ τ) = T(x),
                          S = [τ1/t1],
                          sub(S,ti_,ti2),
                          (idx(l,ti2,Ï) ; member(Ï:idx(l,ti2,L)))
c(L,T,CB,CB) :- cb(CB).
c(L,T,λ(x:τ,M), λ(x,M_)):- c(L,[x:τ|T],M,M_).
c(L,T,(M1$M2), (M1_$M2_)) :- c(L,T,M1,M1_), c(L,T,M2,M2_).
c(L,T,LMs,Cs):- maplist([_=Mi,Ci]>>c(L,T,Mi,Ci),LMs,Cs).
c(L,T,M:τ#l,C#[Ï]) :- c(L,T,M,C), (idx(l,τ,Ï) ; member(Ï:idx(l,τ,L))).
c(L,T,modify(M1:τ,l,M2),modify(C1,Ï,C2)) :- c(L,T,M1,C1), c(L,T,M2,C2), (idx(l,τ,Ï);member(Ï:idx(l,τ),L)).
c(L,T,({[l=M]}:τ),{[Ï=C]}) :- c(L,T,M,C), (idx(l,τ,Ï); member(Ï:idx(l,τ),L)).                  
c(L,T,case(M,{lMs}), switch(C,Cs)) :- c(L,T,M,C), maplist({L,T}[li=Mi,Ci]>>c(L,T,Mi,Ci), lMs,Cs).
c(L,T,poly(M1:∀t1::k1···∀tn::kn.τ1), λI1···λIm.C1) :-
  let ∀t1::k1···∀tn::kn.idx(l1,ti_) ⇒ idx(lm,tm_) ⇒ τ1 = (∀t1::k1···∀tn::kn.τ1)∗
      c(L{I1:idx(l1,t1_),···,In:idx(lm,tm_)},T,M1,C1) (I1,···,Im fresh)
c(L,T,(let(x:σ=M1);M2),(let(x=C1);C2)) :- c(L,T,M1,C1),c(L,[x:(σ)∗|T],M2,C2).

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si::K|Ks_],[Si/T_|S_])) :-
  fresh(Si),foldxq(((X$Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).
:- end_var_names(_).
