% 4. COMPILATION
% implementation calculs system

:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,⟹*,⟹,⟶,⟶*,⊢,▷]).
:- op(1200,xfx,[--]).
:- op(700,xfx,[*=]).
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
    | modify('C','Ï','C') | {['Ï'='C']} | switch('C', record('C')) | λI('I','C') | ('C' $ 'Ï').

% Fig. 12. Call-by-value evaluation operational semantics of λlet,[].

v ::= cb | λ(x,'C') | record(v) | {['Ï'=v]} | λI('I','C'). % (for some C' such that C'↓C').%todo
/*EV[] ::= [·] | EV[] C | V EV[] | let x=EV[] in C | {V,···,V,EV[],···} | EV[][Ï]
        | modify(EV[],I,C) | modify(V,Ï,EV[]) | <Ï=EV[]> | switch EV[] of C,···,C
        | EV[] Ï | λI.EV[]*/
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
ev(Vs#[I])                  ⟶ ev(Vi)          :- nth1(I,Vs,Vi).
ev(modify([_ |LS],1,N))     ⟶ ev([N|LS]).
ev(modify([Mi|LS],I,N))     ⟶ ev([Mi|LS_])    :- I > 1, I_ is I - 1, ev(modify(LS,I_,N)) ⟶ ev(LS_).
ev(switch({[I=V]},Cs))      ⟶ ev(Ci $ V)      :- nth1(I,Cs,Ci).
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
csub(S,{[I=C]},{[I_=C_]}) :- csub(S,I,I_),csub(S,C,C_).
csub(S,switch(C,Cs),switch(C_,Cs_)) :- csub(S,C,C_),maplist({S}/[Ci,Ci_]>>csub(S,Ci,Ci_),Cs,Cs_).

% 4.2 The Type System of λlet,[]

l ::= atom.
b ::= int | bool.
syntax(t). t(T) :- atom(T), \+b(T). 

τ ::= b | t | (τ->τ) | record(l:τ) | variant(l:τ) | idx(l,τ,τ).
k ::= u | record(l::τ) | variant(l::τ). % same as those of `λlet,#`
σ ::= τ | ∀(t,k,σ).

% Fig. 6. Kinding rules for the ML-style type inference system λlet,#.

:- begin_var_names(['^[τtxσkli]'],['^(true|bool|int)$']).

_ ⊢ τ::u :- τ(τ).
K ⊢ t::ks :- t(t),member(t::ks1,K),append(ks,_,ks1), ks \= [].
_ ⊢ ts::ks :- maplist([l:t,k::t]>>!,ts,ks1), append(ks,_,ks1), ks \= [].
_ ⊢ ts::[li::ti] :- member(li:ti,ts).
K ⊢ t::{ks} :- t(t),member(t::{ks1},K),append(ks,_,ks1), ks \= [].
_ ⊢ {ts}::{ks} :-  maplist([l:t,k::t]>>!,ts,ks1),append(ks,_,ks1), ks \= [].
_ ⊢ {ts}::{[li::ti]} :- member(li:ti,ts).

% Fig. 13. Typing rules for the implementation calculus λlet,[].

% L ⊢ Ï : idx(l,τ)   index judgment

L ⊢ I : idx(l,τ) :- 'I'(I), member(I:idx(l,τ),L),l(l),τ(τ). % IVAR
_ ⊢ i : idx(li,Record) :- i(i),nth1(i,Record,li:_). % ICONST1
_ ⊢ i : idx(li,{Variant}) :- i(i),nth1(i,Variant,li:_). % ICONST2

% ------------------------------
% compiler
% ------------------------------

'M' ::= x | 'M'!q | cb | λ(x:q,'M') | ('M' $ 'M') | poly('M':q) | (let(x:q = 'M');'M')
    | record(l='M') | ('M':q) # l | modify('M':q,l,'M')
    | ({[l='M']}:q) | case('M',variant(l='M')).

% 4.3 Compilation Algorithm

idxSet(t::u,[]).
idxSet(t::F,Is) :- maplist([L:_,I]>>idx(L,t,I),F,Is).
idxSet(t::{F},Is) :- maplist([L:_,I]>>idx(L,t,I),F,Is).
idxSet(∀(t,k,τ),Is) :- idSet(t::k,Is1),idxSet(τ,Is2),union(Is1,Is2,Is).
idxSet(K,Is) :- foldl([t::k,Is1,Is3]>>(idxSet(t::k,Is2),union(Is1,Is2,Is3)),K,[],Is).

/*λlet,# で与えられた型 `σ` について、 λlet,[] の対応する型 `(σ)*` は以下のように定義され

    (∀t1::k1···tn::kn.τ)* = ∀t1::k1···tn::kn.idx(l1,t1')⇒···idx(lm,tm')⇒τ

  `idx(l1,t1'),···,idx(lm,tm')` は次のように順序付けられた `IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)` のインデックス型の集合です: `i < j` または `i = j` かつ `l << l'` ならば、 `idx(l,ti)`は `idx(l',tj)` に先行します。
  特に、任意の単相型 `τ` について、`(τ)* = τ` です。
以下はその例です。

∀(t2,[a::bool,b::int],∀(t3,[a::t2],t2->t3)) *=
  ∀(t2,[a::bool,b::int],∀(t3,[a::t2],idx(a,t2,idx(b,t2,idx(a,t3,t2->t3))))) */

getT(∀(ti,ki,t),[ti::ki_|L],T) :- sort(ki,ki_),getT(t,L,T).
getT(T,[],T).
Q *= R :- getT(Q,L,T),foldr(bbb1,L,T,T_),foldr([t::K,T1,∀(t,K,T1)]>>!,L,T_,R).
bbb1(t::K,T,R) :- foldr([li::ti,T1,idx(li,t,T1)]>>!,K,T,R).

/*
  この定義は、次のように型の割り当てに拡張されます:

    (T)* = {x : (T(x))* |x ∈ dom(T)}

  kind 割り当て `K` に対して、 `K` によって決定されるインデックス割り当て `LK` を `LK = {I : idx(l,t)|idx(l,t) ∈ IdxSet(K),each I fresh}` として定義します。
  コンパイルアルゴリズムは、図15において、 `LK,(T)*` および `M` をとり、実装計算の項を計算するアルゴリズム `C` として与えられます。
  `LK` は任意の対 `(l,t)` に対して多くても1つの `(I,idx(l,t)) ∈ LK` があるという性質を持っているので、 したがって、 `C` は決定論的アルゴリズムです。

  このコンパイルでは、次の定理に示すように型が保持されます。
*/
xts(Ts,x,x!Ts) :- x(x),!.
xts(Ts,M!T,M_) :- xts([T|Ts],M,M_),!.

c(_,_,x,x) :- x(x).
c(_,_,CB,CB) :- cb(CB).
c(L,T,λ(x:τ,M), λ(x,M_)):- c(L,[x:τ|T],M,M_).
c(L,T,(M1$M2), (M1_$M2_)) :- c(L,T,M1,M1_), c(L,T,M2,M2_).
c(L,T,LMs,Cs):- maplist([_=Mi,Ci]>>c(L,T,Mi,Ci),LMs,Cs).
c(L,T,M:τ#l,C#[Ï]) :- c(L,T,M,C), (idx(l,τ,Ï) ; member(Ï:idx(l,τ,L))).
c(L,T,modify(M1:τ,l,M2),modify(C1,Ï,C2)) :- c(L,T,M1,C1), c(L,T,M2,C2), (idx(l,τ,Ï);member(Ï:idx(l,τ),L)).
c(L,T,({[l=M]}:τ),{[Ï=C]}) :- c(L,T,M,C), (idx(l,τ,Ï); member(Ï:idx(l,τ),L)).                  
c(L,T,case(M,{lMs}), switch(C,Cs)) :- c(L,T,M,C), maplist({L,T}/[li=Mi,Ci]>>c(L,T,Mi,Ci), lMs,Cs).

% コンパイルでたしか、レコードフィールドにアクセスする関数をまとめるとかだったはず
/*
    C(L,T,Poly(M1:∀t1::k1···∀tn::kn.τ1)) =
      let ∀t1::k1···∀tn::kn.idx(l1,ti') ⇒ idx(lm,tm') ⇒ τ1
             = (∀t1::k1···∀tn::kn.τ1)∗
          C1 = C(L{I1:idx(l1,t1'),···,In:idx(lm,tm')},T,M1) (I1,···,Im fresh)
      in λI1···λIm.C1
*/
/*
c(L,T,poly(M1:∀t1::k1···∀tn::kn.τ1), λI1···λIm.C1) :-
  let ∀t1::k1···∀tn::kn.idx(l1,ti_) ⇒ idx(lm,tm_) ⇒ τ1 = (∀t1::k1···∀tn::kn.τ1)∗
      c(L{I1:idx(l1,t1_),···,In:idx(lm,tm_)},T,M1,C1) (I1,···,Im fresh)
*/
%c(L,T,(let(x:σ=M1);M2),(let(x=C1);C2)) :- c(L,T,M1,C1),c(L,[x:(σ)∗|T],M2,C2).
/*
C(L,T,(x τ1···τn)) =
  let (∀t1::k1 ···tn::kn.idx(l1,t1') ⇒···idx(lm,tm') ⇒ τ) = T(x) 関数を取り出して
                          S = [τ1/t1,···,τn/tn]
                          Ïi = | i if |idx(l,S(ti'))| = i
                                | I if |idx(l,S(ti'))| is undefined and (I:idx(l,S(ti'))) ∈ L
                      in (x Ï1···Ïm)
*/
c(L,T,(x1!τ1), (x!Ï1)) :- xts([],x1!τ1,x!τs), member(x: ∀(t1,k1,(idx(l1,t1_) -> τ)), T),
                        sub([τ1/t1],ti_,ti2),
                        (idx(l,ti2,Ï) ; member(Ï:idx(l,ti2,L))).

foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si::K|Ks_],[Si/T_|S_])) :-
  fresh(Si),foldxq(((X$Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

:- end_var_names(_).
