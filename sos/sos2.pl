% Second-Order System Λ∀,#
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!]).
:- op(920,xfx,[⟹,▷,⊢,⟹*]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
term_expansion(A--B,R) :- next_term_expansion(B:-A,R).
% Syntaxs

syntax(k).
syntax(t). t(T) :- atom(T), \+b(T). 
b ::= int | bool.
l ::= atom.
list(A) ::= [] | [A | list(A)].
record(A) ::= list(A).
variant(A) ::= {list(A)}.
σ ::= b | t | (σ->σ) | record(l:σ) | variant(l:σ) | ∀(t,k,σ).
k ::= u | record(l:σ) | variant(l:σ).
syntax(integer).
syntax(x). x(X) :- atom(X), \+cb(X).
i ::= integer.
cb ::= true | false | i.
'M' ::= x | cb | λ(x:σ,'M') | ('M' $ 'M') | λ(t::k,'M') | ('M' ! σ)
    | record(l='M') | 'M'#l | modify('M',l,'M')
    | {[l='M']}:σ | case('M',variant(l='M')).
q(Q) :- σ(Q).
m(M) :- 'M'(M).
:- begin_var_names(['^[σlxktcbi]'],['^(true|bool|int)$']).

% Kinding rules

K ⊢     t : lσs  :- member(t:lσ2s,K), intersection(lσ2s,lσs,lσs).
_ ⊢  lσ2s : lσs  :- intersection(lσ2s,lσs,lσs).
K ⊢     t :{lσs} :- member(t:{lσ2s},K), intersection(lσ2s,lσs,lσs).
_ ⊢ {lσ2s}:{lσs} :- intersection(lσ2s,lσs,lσs).
_ ⊢     _ : u.

% Substitutions

tsub(S,t,N_) :- t(t),member(N/t,S),!,tsub(S,N,N_).
tsub(_,t,t) :- t(t),!.
tsub(_,b,b) :- b(b),!.
tsub(S,(σ1->σ2),(σ1_->σ2_)) :- tsub(S,σ1,σ1_),tsub(S,σ2,σ2_).
tsub(S,lMs,lMs_) :- maplist({S}/[l:M,l:M_]>>tsub(S,M,M_),lMs,lMs_).
tsub(S,{lMs},{lMs_}) :- maplist({S}/[l:M,l:M_]>>tsub(S,M,M_),lMs,lMs_).
tsub(S,∀(t,k,σ),∀(t,k_,σ_)) :- subtract(S,[_/t],S_),ksub(S_,k,k_),tsub(S_,σ,σ_).

ksub(_,u,u).
ksub(S,lσs,lσs_) :- maplist({S}/[l:σ,l:σ_]>>tsub(S,σ,σ_), lσs,lσs_).
ksub(S,{lσs},{lσs_}) :- maplist({S}/[l:σ,l:σ_]>>tsub(S,σ,σ_), lσs,lσs_).

msub(S,x,N_) :- x(x),member(N/x,S),!,msub(S,N,N_).
msub(_,x,x) :- x(x),!.
msub(_,cb,cb) :- cb(cb),!.
msub(S,λ(x:σ,M),λ(x:σ,M_)) :- subtract(S,[_/x],S_),!,msub(S_,M,M_).
msub(S,(M1$M2),(M1_$M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,(M!σ),(M_!σ)) :- msub(S,M,M_).
msub(S,λ(t::k,M),λ(t::k,M_)) :- msub(S,M,M_).
msub(S,lMs,lMs_) :- maplist({S}/[l=M,l=M_]>>msub(S,M,M_),lMs,lMs_).
msub(S,(M#l),(M_#l)) :- msub(S,M,M_).
msub(S,modify(M1,l,M2),modify(M1_,l,M2_)) :- msub(S,M1,M1_), msub(S,M2,M2_).
msub(S,{[l=M]}:σ,{[l=M_]}:σ) :- msub(S,M,M_).
msub(S,case(M,{lMs}),case(M_,{lMs_})) :- msub(S,M,M_),maplist({S}/[l=Mi,l=Mi_]>>msub(S,Mi,Mi_),lMs,lMs_).

mtsub(S,λ(x:σ,M),λ(x:σ_,M_)) :- tsub(S,σ,σ_),mtsub(S,M,M_).
mtsub(S,(M1$M2),(M1_$M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,(M!σ),(M_!σ_)) :- mtsub(S,M,M_), tsub(S,σ,σ_).
mtsub(S,λ(t::k,M),λ(t_::k_,M_)) :- subtract(S,[_/t],S_),tsub(S_,t,t_),ksub(S_,k,k_),mtsub(S_,M,M_).
mtsub(S,lMs,lMs_) :- maplist({S}/[l=M,l=M_]>>mtsub(S,M,M_),lMs,lMs_).
mtsub(S,(M#l),(M_#l)) :- mtsub(S,M,M_).
mtsub(S,modify(M1,l,M2),modify(M1_,l,M2_)) :- mtsub(S,M1,M1_), mtsub(S,M2,M2_).
mtsub(S,{[l=M]}:σ,{[l=M_]}:σ) :- mtsub(S,M,M_).
mtsub(S,case(M,{lMs}),case(M_,{lMs_})) :- mtsub(S,M,M_),maplist({S}/[l=Mi,l=Mi_]>>mtsub(S,Mi,Mi_),lMs,lMs_).
mtsub(_,M,M).

% Reduction rules

(λ(x:_,M)$N)             ⟹ M_              :- msub([N/x], M,M_).       % (β)
(λ(t::_,M)!σ)            ⟹ M_              :- mtsub([σ/t], M,M_).      % (type-β)
lMs#li                   ⟹ Mi              :- member(li=Mi,lMs).       % (dot)
modify([li=_ |lMs],li,N) ⟹ [li=N|lMs].                                 % (modify)
modify([li=Mi|lMs],l,N)  ⟹ [li=Mi|lMs_]    :- modify(lMs,l,N) ⟹ lMs_.% (modify)
case({[li=M]}:_, {lMs})  ⟹ (Mi $ M)        :- member(li=Mi,lMs).       % (case)
(M $ N)                  ⟹ (M_ $ N)        :- M ⟹ M_.
(M ! σ)                  ⟹ (M_ ! σ)        :- M ⟹ M_.
modify(M,l,N)            ⟹ modify(M_,l,N)  :- M ⟹ M_.
case(M, {lMs})           ⟹ case(M_, {lMs}) :- M ⟹ M_.

M ⟹* M_ :- M ⟹ M1,!, M1 ⟹* M_.
M ⟹* M.

% Free Type variables

ftv(x,[x]) :- x(x).
ftv(B,[]) :- b(B).
ftv((σ1->σ2),FTV) :- ftv(σ1,FTV1),ftv(σ2,FTV2),union(FTV1,FTV2,FTV).
ftv(lMs,FTVs) :- foldl([_=M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),lMs,[],FTVs).
ftv({lMs},{FTVs}) :- foldl([_=M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),lMs,[],FTVs).
ftv(∀(t,k,σ),FTV) :- kftv(k,KFTV),ftv(σ,QFTV),union(KFTV,QFTV,FTV1),subtract(FTV1,t,FTV).

kftv(u,[]).
kftv(lσs,FTVs) :- foldl([_:σ,FTV,FTV_]>>(ftv(σ,FTVi),union(FTV,FTVi,FTV_)),lσs,[],FTVs).
kftv({lσs},FTVs) :- foldl([_:σ,FTV,FTV_]>>(ftv(σ,FTVi),union(FTV,FTVi,FTV_)),lσs,[],FTVs).
tftv(lσs,FTVs) :- foldl([_:σ,FTV,FTV_]>>(ftv(σ,FTVi),union(FTV,FTVi,FTV_)),lσs,[],FTVs).

% Type system

(_,T) ▷ x : σ    :- member(x:σ,T).                            % VAR
(_,_) ▷ i : int  :- i(i).                                     % CONST
(_,_) ▷ true  : bool.                                         % CONST
(_,_) ▷ false : bool.                                         % CONST

(K,[x:σ1|T]) ▷ M1 : σ2
--%------------------------------------------------------------ ABS
(K,T) ▷ λ(x:σ1,M1) : (σ1->σ2).

(K,T) ▷ M1 : (σ1->σ2),  (K,T) ▷ M2 : σ1
--%------------------------------------------------------------ APP
(K,T) ▷ (M1 $ M2) : σ2.

tftv(T,FTV),  \+member(t,FTV),  ([t:k|K],T) ▷ M : σ
--%------------------------------------------------------------ TABS
(K,T) ▷ λ(t::k,M) : ∀(t,k,σ).

(K,T) ▷ M : ∀(t,k,σ1),  K ⊢ σ2:k,  tsub([σ2/t],σ1,σ1_)
--%------------------------------------------------------------ TAPP
(K,T) ▷ (M ! σ2) : σ1_.

maplist({K,T}/[li=Mi,li:σi]>>((K,T) ▷ Mi : σi), lMs, lσs)
--%------------------------------------------------------------ RECORD
(K,T) ▷ lMs : lσs.

(K,T) ▷ M : σ1,   K ⊢ σ1:[l:σ2]
--%------------------------------------------------------------ DOT
(K,T) ▷ (M # l) : σ2.

(K,T) ▷ M1 : σ1,  (K,T) ▷ M2 : σ2,  K ⊢ σ1:[l:σ2]
--%------------------------------------------------------------ MODIFY
(K,T) ▷ modify(M1,l,M2) : σ1.

(K,T) ▷ M : σ1,  K ⊢ σ2:{[l:σ1]}
--%------------------------------------------------------------ VARIANT
(K,T) ▷ ({[l=M]}:σ2) : σ2.

(K,T) ▷ M : {lσs},
maplist({K,T,σ}/[li=Mi,li:σi]>>((K,T) ▷ Mi : (σi->σ)),lMs,lσs)
--%------------------------------------------------------------ CASE
(K,T) ▷ case(M,{lMs}) : σ.

:- end_var_names(_).
