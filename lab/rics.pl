% 4. COMPILATION
% implementation calculs system

:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,⟹*,⟹,⟶,⟶*,⊢,▷]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
term_expansion(A--B,B:-A).

foldr(_,[],S,S) :- !. % 畳み込み
foldr(F,[X|Xs],S,S_) :- foldr(F,Xs,S,S1),!,call(F,X,S1,S_),!.

list(A) ::= [] | [A | list(A)].
record(A) ::= list(A).
variant(A) ::= {list(A)}.

% 4.1 Implementation Calculus : λlet,[]

syntax(integer).
syntax(x). x(X) :- atom(X), \+cb(X).
i ::= integer. % i for natural numbers.
cb ::= true | false | i.
'I' ::= atom. % I stands for a given set of index variables and
'Ï' ::= 'I' | i.
'C' ::= x | cb |λ(x,'C') | ('C' $ 'C') | (let(x='C'); 'C') | record('C') | 'C'#['Ï']
    | modify('C','Ï','C') | λI('I','C') | ('C' $ 'Ï').

% Fig. 12. Call-by-value evaluation operational semantics of λlet,[].

v ::= cb | λ(x,'C') | record(v) | λI('I','C'). % (for some C' such that C'↓C').%todo
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
ev(Vs#[I])                  ⟶ ev(Vi)          :- nth1(I,Vs,Vi).
ev(modify([_ |LS],1,N))     ⟶ ev([N|LS]).
ev(modify([Mi|LS],I,N))     ⟶ ev([Mi|LS_])    :- I > 1, I_ is I - 1, ev(modify(LS,I_,N)) ⟶ ev(LS_).
ev(λ(I,C)$Ï)                ⟶ ev(C_)          :- 'Ï'(Ï),csub([Ï/I],C,C_).
ev(let(X = V); C)           ⟶ ev(C_)          :- csub([V/X],C,C_).

ev(C) ⟹ ev(C_) :- ev(H/R,C,C_), ev(R) ⟶ ev(H).
ev(C) ⟹ ev(C_) :- ev(C) ⟶ ev(C_).
C ⟹* C_ :- ev(C) ⟹ ev(C1),!, C1 ⟹* C_.
C ⟹* C.

csub(S,X,N_) :- member(N/X,S),!,csub(S,N,N_).
csub(_,X,X) :- x(X),!.
csub(_,CB,CB) :- cb(CB),!.
csub(S,λ(X,C),λ(X,C_)) :- !,subtract(S,[_/X],S_),csub(S_,C,C_).
csub(S,λI(X,C),λI(X,C_)) :- !,subtract(S,[_/X],S_),csub(S_,C,C_).
csub(S,(C1$C2),(C1_$C2_)) :- csub(S,C1,C1_), csub(S,C2,C2_).
csub(S,Cs,Cs_) :- maplist({S}/[C,C_]>>csub(S,C,C_),Cs,Cs_).
csub(S,(C#[I]),(C_#[I_])) :- !,csub(S,C,C_),csub(S,I,I_).
csub(S,modify(C1,I,C2),modify(C1_,I,C2_)) :- csub(S,C1,C1_), csub(S,C2,C2_).

% 4.2 The Type System of λlet,[]

l ::= atom.
b ::= int | bool.
syntax(t). t(T) :- atom(T), \+b(T). 

τ ::= b | t | (τ->τ) | record(l:τ) |  idx(l,τ,τ).
k ::= u | record(l::τ). % same as those of `λlet,#`
σ ::= τ | ∀(t,k,σ).

% Fig. 6. Kinding rules for the ML-style type inference system λlet,#.

:- begin_var_names(['^[τtxσkli]'],['^(true|bool|int)$']).

_ ⊢ τ::u :- τ(τ).
K ⊢ t::ks :- t(t),member(t::ks1,K),append(ks,_,ks1), ks \= [].
_ ⊢ ts::ks :- maplist([l:t,k::t]>>!,ts,ks1), append(ks,_,ks1), ks \= [].
_ ⊢ ts::[li::ti] :- member(li:ti,ts).

% Fig. 13. Typing rules for the implementation calculus λlet,[].

% L ⊢ Ï : idx(l,τ)   index judgment

L ⊢ I : idx(l,τ) :- 'I'(I), member(I:idx(l,τ),L),l(l),τ(τ). % IVAR
_ ⊢ i : idx(li,Record) :- i(i),nth1(i,Record,li:_). % ICONST1

% K,L,T ▷ C : τ       typing judgment

member(x:σ, T), /* とりあえず */ σ=τ /*, K ⊢ σ ≥ τ
% if T{x:σ} and L are well formed under K and K ⊢ σ ≥ τ*/
--%---------------------------------------------------------- VAR
(K,L,T) ▷ x : τ.

(_,_,_) ▷ true : bool.     % CONST
(_,_,_) ▷ false : bool.    % CONST
(_,_,_) ▷ i : int :- i(i). % CONST

(K,L,T) ▷ C1 : (τ1->τ2),  (K,L,T) ▷ C2 : τ1
--%------------------------------------------ APP
(K,L,T) ▷ (C1 $ C2) : τ2.

(K,L,[x:τ1|T]) ▷ C1 : τ2
--%------------------------------------------ ABS
(K,L,T) ▷ λ(x,C1) : (τ1->τ2).

/*(K,[I:idx(l,τ1)|L],T) ▷ C1 : τ2
--%---------------------------------------------------------- IABS
(K,L,T) ▷ λ(I,C1) : idx(l,τ1) ⇒ τ2.

(K,L,T) ▷ C : idx(l,τ1) ⇒ τ2,    L ⊢ Ï : idx(l,τ1)
--%---------------------------------------------------------- IAPP
(K,L,T) ▷ C Ï : τ2.*/

maplist([Ci,li:τi]>>((K,L,T) ▷ Ci : τi),Record,τ)
--%---------------------------------------------------------- RECORD
(K,L,T) ▷ Record : τ.

(K,L,T) ▷ C1 : τ1, K ⊢ τ1::[l::τ2], L ⊢ Ï : idx(l,τ1)
--%---------------------------------------------------------- INDEX
(K,L,T) ▷ (C1#[Ï]) : τ2.

(K,L,T) ▷ C1 : τ1,  K ⊢ τ1::[l::τ2],
L ⊢ Ï : idx(l,τ1),  (K,L,T) ▷ C2 : τ2
--%---------------------------------------------------------- MODIFY
(K,L,T) ▷ modify(C1,Ï,C2) : τ1.

/*(K[t1::k1···tn::kn],L,T) ▷ C : τ  % if ti ∉ FTV(L ∪ T) (1 ≤ i ≤ n)
--%---------------------------------------------------------- GEN 
(K,L,T) ▷ C : ∀([t1::kn,···,tn::kn],τ).*/

(K,L,T) ▷ C1 : σ,   (K,L,[x:σ|T]) ▷ C2 : τ
--%---------------------------------------------------------- LET
(K,L,T) ▷ (let(x=C1);C2) : τ.

:- end_var_names(_).
