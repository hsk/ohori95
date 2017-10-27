% Second-Order System Λ∀,#
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,▷,⊢,⟹*]).
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
m ::= x | cb | λ(x:q,m) | (m $ m) | λ(t::k,m) | (m ! q)
    | record(l=m) | m#l | modify(m,l,m)
    | {[l=m]}:q | case(m,variant(l=m)).

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
tsub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>tsub1(S,N/X,M,M_),LMs,LMs_).
tsub1(S,N/X,{LMs},{LMs_}) :- maplist({S,N,X}/[L=M,L=M_]>>tsub1(S,N/X,M,M_),LMs,LMs_).
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
msub1(_,_/X,λ(X:Q,M),λ(X:Q,M)).
msub1(S,N/X,λ(X1:Q,M),λ(X1:Q,M_)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,(M1$M2),(M1_$M2_)) :- m(M2),msub1(S,N/X,M1,M1_), msub1(S,N/X,M2,M2_).
msub1(S,N/X,(M!Q),(M_!Q)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,λ(T::K,M),λ(T::K,M_)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>msub1(S,N/X,M,M_),LMs,LMs_).
msub1(S,N/X,(M#L),(M_#L)) :- msub1(S,N/X,M,M_).
msub1(S,N/X,modify(M1,L,M2),modify(M1_,L,M2_)) :- msub1(S,N/X,M1,M1_), msub1(S,N/X,M2,M2_).
msub1(S,N/X,{[L=M]}:Q,{[L=M_]}:Q) :- msub1(S,N/X,M,M_).
msub1(S,N/X,case(M,{LMs}),case(M_,{LMs_})) :- msub1(S,N/X,M,M_),maplist({S,N,X}/[L=Mi,L=Mi_]>>msub1(S,N/X,Mi,Mi_),LMs,LMs_).

mtsub(S,M,M_) :- foldl(mtsub1(S),S,M,M_),!.
mtsub1(S,N/X,X,N_) :- mtsub(S,N,N_).
mtsub1(S,N/X,λ(X1:Q,M),λ(X1:Q_,M_)) :- tsub1(S,N/X,Q,Q_),mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,(M1$M2),(M1_$M2_)) :- m(M2),mtsub1(S,N/X,M1,M1_), mtsub1(S,N/X,M2,M2_).
mtsub1(S,N/X,(M!Q),(M_!Q_)) :- mtsub1(S,N/X,M,M_), tsub1(S,N/X,Q,Q_).
mtsub1(_,_/X,λ(X::K,M),λ(X::K,M)).
mtsub1(S,N/X,λ(T::K,M),λ(T_::K_,M_)) :- tsub1(S,N/X,T,T_),ksub1(S,N/X,K,K_),mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,LMs,LMs_) :- maplist({S,N,X}/[L=M,L=M_]>>mtsub1(S,N/X,M,M_),LMs,LMs_).
mtsub1(S,N/X,(M#L),(M_#L)) :- mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,modify(M1,L,M2),modify(M1_,L,M2_)) :- mtsub1(S,N/X,M1,M1_), mtsub1(S,N/X,M2,M2_).
mtsub1(S,N/X,{[L=M]}:Q,{[L=M_]}:Q) :- mtsub1(S,N/X,M,M_).
mtsub1(S,N/X,case(M,{LMs}),case(M_,{LMs_})) :- mtsub1(S,N/X,M,M_),maplist({S,N,X}/[L=Mi,L=Mi_]>>mtsub1(S,N/X,Mi,Mi_),LMs,LMs_).
mtsub1(_,_/_,M,M).

% Reduction rules

(λ(X:_,M)$N)            ⟹ M_             :- msub([N/X], M,M_).      % (β)
(λ(T::_,M)!Q)           ⟹ M_             :- mtsub([Q/T], M,M_).     % (type-β)
LS#Li                   ⟹ Mi             :- member(Li=Mi,LS).       % (dot)
modify([Li=_ |LS],Li,N) ⟹ [Li=N|LS].                                % (modify)
modify([Li=Mi|LS],L,N)  ⟹ [Li=Mi|LS_]    :- modify(LS,L,N) ⟹ LS_. % (modify)
case({[Li=M]}:_, {Ls})  ⟹ (Mi $ M)       :- member(Li=Mi,Ls).       % (case)
(M $ N)                 ⟹ (M_ $ N)       :- M ⟹ M_.
(M ! Q)                 ⟹ (M_ ! Q)       :- M ⟹ M_.
modify(M,L,N)           ⟹ modify(M_,L,N) :- M ⟹ M_.
case(M, {Ls})           ⟹ case(M_, {Ls}) :- M ⟹ M_.

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

(_,T) ▷ X : Q    :- member(X:Q,T).                            % VAR
(_,_) ▷ I : int  :- i(I).                                     % CONST
(_,_) ▷ true  : bool.                                         % CONST
(_,_) ▷ false : bool.                                         % CONST

(K,[X:Q1|T]) ▷ M1 : Q2
--%------------------------------------------------------------ ABS
(K,T) ▷ λ(X:Q1,M1) : (Q1->Q2).

(K,T) ▷ M1 : (Q1->Q2),  (K,T) ▷ M2 : Q1
--%------------------------------------------------------------ APP
(K,T) ▷ (M1 $ M2) : Q2.

tftv(T,FTV),  \+member(T_,FTV),  ([T_::K_|K],T) ▷ M : Q
--%------------------------------------------------------------ TABS
(K,T) ▷ λ(T_::K_,M) : ∀(T_,K_,Q).

(K,T) ▷ M : ∀(T_,K_,Q1),  K ⊢ Q2::K_,  tsub([Q2/T_],Q1,Q1_)
--%------------------------------------------------------------ TAPP
(K,T) ▷ (M ! Q2) : Q1_.

maplist({K,T}/[Li=Mi,Li:Qi]>>((K,T) ▷ Mi : Qi), LMs, LQs)
--%------------------------------------------------------------ RECORD
(K,T) ▷ LMs : LQs.

(K,T) ▷ M : Q1,   K ⊢ Q1::[L:Q2]
--%------------------------------------------------------------ DOT
(K,T) ▷ (M # L) : Q2.

(K,T) ▷ M1 : Q1,  (K,T) ▷ M2 : Q2,  K ⊢ Q1::[L:Q2]
--%------------------------------------------------------------ MODIFY
(K,T) ▷ modify(M1,L,M2) : Q1.

(K,T) ▷ M : Q1,  K ⊢ Q2::{[L:Q1]}
--%------------------------------------------------------------ VARIANT
(K,T) ▷ ({[L=M]}:Q2) : Q2.

(K,T) ▷ M : {LQs},
maplist({K,T,Q}/[Li=Mi,Li:Qi]>>((K,T) ▷ Mi : (Qi->Q)),LMs,LQs)
--%------------------------------------------------------------ CASE
(K,T) ▷ case(M,{LMs}) : Q.
