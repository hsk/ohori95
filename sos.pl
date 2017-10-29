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

tsub(S,X,N_) :- t(X),member(N/X,S),tsub(S,N,N_).
tsub(_,X,X) :- t(X).
tsub(_,B,B) :- b(B).
tsub(S,(Q1->Q2),(Q1_->Q2_)) :- tsub(S,Q1,Q1_),tsub(S,Q2,Q2_).
tsub(S,LMs,LMs_) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,{LMs},{LMs_}) :- maplist({S}/[L:M,L:M_]>>tsub(S,M,M_),LMs,LMs_).
tsub(S,∀(T,K,Q),∀(T,K_,Q_)) :- subtract(S,[_/T],S_),ksub(S_,K,K_),tsub(S_,Q,Q_).

ksub(_,u,u).
ksub(S,LQs,LQs_) :- maplist({S}/[L:Q,L:Q_]>>tsub(S,Q,Q_), LQs,LQs_).
ksub(S,{LQs},{LQs_}) :- maplist({S}/[L:Q,L:Q_]>>tsub(S,Q,Q_), LQs,LQs_).

msub(S,X,N_) :- x(X),member(N/X,S),!,msub(S,N,N_).
msub(_,X,X) :- x(X),!.
msub(_,CB,CB) :- cb(CB),!.
msub(S,λ(X:Q,M),λ(X:Q,M_)) :- !,subtract(S,[_/X],S_),msub(S_,M,M_).
msub(S,(M1$M2),(M1_$M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,(M!Q),(M_!Q)) :- msub(S,M,M_).
msub(S,λ(T::K,M),λ(T::K,M_)) :- msub(S,M,M_).
msub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>msub(S,M,M_),LMs,LMs_).
msub(S,(M#L),(M_#L)) :- msub(S,M,M_).
msub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,{[L=M]}:Q,{[L=M_]}:Q) :- msub(S,M,M_).
msub(S,case(M,{LMs}),case(M_,{LMs_})) :- msub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_).

mtsub(S,X,N_) :- t(X),member(N/X,S),mtsub(S,N,N_).
mtsub(S,λ(X:Q,M),λ(X:Q_,M_)) :- tsub(S,Q,Q_),mtsub(S,M,M_).
mtsub(S,(M1$M2),(M1_$M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,(M!Q),(M_!Q_)) :- mtsub(S,M,M_), tsub(S,Q,Q_).
mtsub(S,λ(T::K,M),λ(T_::K_,M_)) :- subtract(S,[_/T],S_),tsub(S_,T,T_),ksub(S_,K,K_),mtsub(S_,M,M_).
mtsub(S,LMs,LMs_) :- maplist({S}/[L=M,L=M_]>>mtsub(S,M,M_),LMs,LMs_).
mtsub(S,(M#L),(M_#L)) :- mtsub(S,M,M_).
mtsub(S,modify(M1,L,M2),modify(M1_,L,M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,{[L=M]}:Q,{[L=M_]}:Q) :- mtsub(S,M,M_).
mtsub(S,case(M,{LMs}),case(M_,{LMs_})) :- mtsub(S,M,M_),maplist({S}/[L=Mi,L=Mi_]>>mtsub(S,Mi,Mi_),LMs,LMs_).
mtsub(_,M,M).

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
