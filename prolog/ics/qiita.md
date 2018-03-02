# Implementation Calculs System

ここでは、多相レコードのコンパイル後のシステム`λlet[]`のコンパイラを省いた物を見ていきます。

## `λlet[]` の実装

```prolog:ics.pl
% implementation calculs system
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!,⊆]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,⟹*,⟹,⟶,⟶*,⊢,▷]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
term_expansion(A--B,B:-A).
```

例によってまず、演算子の定義とモジュール読み込みをします。

```prolog
foldr(_,[],S,S) :- !. % 畳み込み
foldr(F,[X|Xs],S,S_) :- foldr(F,Xs,S,S1),!,call(F,X,S1,S_),!.
```

foldrを定義します。

構文

```prolog
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
```

コンパイル後の言語は `C` で表します。

```prolog
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
```

評価規則は、評価文脈とスモールステップ評価器からできていて、変更できなくなったら終了です。

```prolog
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
```

csubは評価する際に必要な置換処理です。

これ以降はコンパイルに必要な定義になります。

型の構文は `λlet#` と同じものを用います

```prolog
% 4.2 The Type System of λlet,[]

l ::= atom.
b ::= int | bool.
syntax(t). t(T) :- atom(T), \+b(T). 

τ ::= b | t | (τ->τ) | record(l:τ) | variant(l:τ) | idx(l,τ,τ).
k ::= u | record(l::τ) | variant(l::τ). % same as those of `λlet,#`
σ ::= τ | ∀(t,k,σ).

% Fig. 6. Kinding rules for the ML-style type inference system λlet,#.
```

カインドは以下のような規則で求めます。

```prolog
:- begin_var_names(['^[τtxσkli]'],['^(true|bool|int)$']).

_ ⊢ τ::u :- τ(τ).
K ⊢ t::ks :- t(t),member(t::ks1,K),append(ks,_,ks1), ks \= [].
_ ⊢ ts::ks :- maplist([l:t,k::t]>>!,ts,ks1), append(ks,_,ks1), ks \= [].
_ ⊢ ts::[li::ti] :- member(li:ti,ts).
K ⊢ t::{ks} :- t(t),member(t::{ks1},K),append(ks,_,ks1), ks \= [].
_ ⊢ {ts}::{ks} :-  maplist([l:t,k::t]>>!,ts,ks1),append(ks,_,ks1), ks \= [].
_ ⊢ {ts}::{[li::ti]} :- member(li:ti,ts).

% Fig. 13. Typing rules for the implementation calculus λlet,[].
```

インデックス関数を求めるには以下の規則を用います。

```prolog
% L ⊢ Ï : idx(l,τ)   index judgment

L ⊢ I : idx(l,τ) :- 'I'(I), member(I:idx(l,τ),L),l(l),τ(τ). % IVAR
_ ⊢ i : idx(li,Record) :- i(i),nth1(i,Record,li:_). % ICONST1
_ ⊢ i : idx(li,{Variant}) :- i(i),nth1(i,Variant,li:_). % ICONST2

:- end_var_names(_).
```

## テスト

```prolog
:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(ics).
```

モジュール読み込みをします。

```prolog
:- begin_tests(avs).
  test(i) :- i(1).
  test(i) :- i(10).
  test(i) :- i(-10).
  test(cb) :- cb(-10).
  test(cb) :- cb(true).
  test(cb) :- cb(false).
  test(x) :- x(x).
  test(x) :- \+x(true).
  test(x) :- \+x(1).

  test(c_xcb) :- 'C'(1),'C'(true),'C'(xxx).
  test(c_λ) :- 'C'(λ(x,x)).
  test(c_app) :- 'C'(λ(x,x)$1).
  test(c_λ) :- 'C'(λI(i,i)).
  test(c_record) :- 'C'([1,2]).
  test(c_record) :- 'C'([1,2]#[i]).
  test(c_record) :- 'C'([1,2]#[1]).
  test(c_record) :- 'C'(modify([1,2],1,2)).
  test(c_variant) :- 'C'({[1=1]}).
  test(c_variant) :- 'C'(switch(1,[λ(x,x),λ(x,add$x#[1]$x#[2])])),!.
  
:- end_tests(avs).
```

このような構文が使えます。

```prolog
:- begin_tests(csub).

  test(cb) :- csub([y/x],1,1),csub([y/x],true,true),csub([y/x],false,false).
  test(x) :- csub([y/x],x,y).
  test(x) :- csub([y/x,z/y],x,z).
  test(x) :- csub([z/y,y/x],x,z).
  test(x) :- csub([y/x,z/y],x,z).
  test(x) :- csub([z/y,y/x],x,z).
  test(λ) :- csub([y/x,z/y],λ(x,x),λ(x,x)).
  test(λ) :- csub([y/x,z/y],λ(a,x),λ(a,z)).
  test(λ) :- csub([z/y,y/x],λ(a,x),λ(a,z)).
:- end_tests(csub).
```

置換はこのように動きます。

```prolog
:- begin_tests(eval).
  test(λ) :- λ(x,x) $ 1 ⟹* 1.
  test(record) :- ([10,20]#[1]) ⟹* 10.
  test(record) :- ([10,20]#[2]) ⟹* 20.
  test(record) :- ([(λ(x,x)$11),2]#[1]) ⟹* 11.
  test(record) :- ([(λ(x,x)$11),λ(y,y)$22]#[2]) ⟹* 22.
  test(record) :- (modify([11,22],1,10)) ⟹* [10,22].
  test(record) :- (modify([11,22],2,10)) ⟹* [11,10].
  test(record) :- (λ(z,[z])$10) ⟹* [10].
  test(record) :- (modify((λ(z,[11,z])$10),1,22)) ⟹* R,!,R=[22,10].  
  test(variant) :- ({[1=1]}) ⟹* ({[1=1]}).
  test(variant) :- (switch((λ(z,{[1=z]})$1),[λ(x,x),λ(x,add$x#[1]$x#[2])])) ⟹* 1.
  test(variant) :- (switch((λ(z,{[2=[z,10]]})$1),[λ(x,x),λ(x,[x#[2],x#[1]])])) ⟹* [10,1].
:- end_tests(eval).
```

評価は以上のように動きます。

```prolog
:- begin_tests(τ).
  test(x) :- τ(x).
  test(b) :- τ(int).
  test(fun) :- τ(int->int).
  test(empty_record):- τ([]).
  test(one_element_record):- τ([a:int]).
  test(three_elements_record):- τ([a:int,b:int,c:bool]).
  test(nested_record):- τ([a:int,b:[a:int,c:bool]]).
  test(variant):- τ({[eint:int,eadd:['1':e,'2':e]]}).
  test(idx) :- τ(idx(a,x,int)). % todo
:- end_tests(τ).
```

型の構文は以上のようになります。

```prolog
:- begin_tests(k).
  test(k):- k(u).
  test(k):- k([]).
  test(k):- k([l::int]).
  test(k):- k({[eint::int,eadd::['1':int,'2':int],emul::['1':int,'2':int]]}),!.
:- end_tests(k).
```

カインドの構文は以上のようになります。

```prolog
:- begin_tests(σ).
  test(σ):- σ(∀(t,u,t)).
  test(σ):- σ(∀(t,[a::int,b::int],t)).
  test(σ):- σ(∀(t,{[a::t,b::t]},{[a:t,b:t,c:int]})),!.
  test(σ):- σ(∀(t,[a::t,b::t],[a:t,b:t,c:int])).
  test(fun) :- σ(int->int).
:- end_tests(σ).
```

多相型の構文は以上のようになります。

```prolog
:- begin_tests(kinding).
:- begin_var_names(['^(k|t)[0-9]*$'],['^(true|bool|int)$']).
  test(kinding_int):- [] ⊢ int::k,k=u,!.
  test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[x::int],!.
  test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[x::int,y::int],!.
  % test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[y::int]. todo
  test(kinding_record):- [] ⊢ [x:int,y:int]::k,k=[x::int],!.
  test(kinding_record):- [] ⊢ [x:int,y:int]::k,k=[x::int,y::int],!.
  test(kinding_variant_t):- [a::{[x::int,y::int]}] ⊢ a::k,k={[x::int]},!.
  test(kinding_variant_t):- [a::{[x::int,y::int]}] ⊢ a::k,k={[x::int,y::int]},!.
  test(kinding_variant):- [] ⊢ {[x:int,y:int]}::k,k={[x::int]},!.
  test(kinding_variant):- [] ⊢ {[x:int,y:int]}::k,k={[x::int,y::int]},!.
:- end_var_names(_).
:- end_tests(kinding).
```

カインドの取得は以上のように動きます。

```prolog
:- begin_tests(index_judgment).
  test('IVAR I') :- [k:idx(x,int)] ⊢ k : idx(x,int),!.
  test('IVAR i record') :- [] ⊢ 1 : idx(k,[k:int,j:int]),!.
  test('IVAR i record') :- [] ⊢ 2 : idx(j,[k:int,j:int]),!.
  test('IVAR i variant') :- [] ⊢ 1 : idx(k,{[k:int,j:int]}),!.
  test('IVAR i variant') :- [] ⊢ 2 : idx(j,{[k:int,j:int]}),!.
:- end_tests(index_judgment).
```

インデックス関数の取得、判定は以上のようになるようです。これでいいのかね？

```prolog
:- run_tests.
:- halt.
```

テストの実行とプログラムの終了を最後にします。
