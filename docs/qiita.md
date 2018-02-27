# Prologによる多相レコード計算の実装

激しく締め切りを破り、平昌冬季オリンピックも終わって、もう２月が終わろうとしていますが皆さんいかがお過ごしでしょうか？
とりあえず、気がかりになっていたので、全てではありませんが時を遡ってアドベントカレンダーの最後の記事をアップする次第であります。

ここでは、Prologを用いて Ohori [^1] の多相レコード計算の実装を行います。
多相レコードの論文はかなり細かいところまで書かれているのですが手始めに最初にでてくる簡単な型付きの二階の多相レコード計算システムを実装します。

## 1. Second-Order System Λ∀,# の実装

まずは演算子の優先順位定義と、rtgモジュール読み込み、マクロ定義があります。
rtgモジュールは構文定義をBNF風の記述を可能にするライブラリです。

```prolog:sos.pl
% Second-Order System Λ∀,#
:- op(600,xfx,[::,#]).
:- op(650,yfx,[$,!]).
:- op(600,xfx,[#,::]).
:- op(920,xfx,[⟹,▷,⊢,⟹*]).
:- op(1200,xfx,[--]).
:- use_module(rtg).
term_expansion(A--B,R) :- next_term_expansion(B:-A,R).
```

構文定義

```prolog
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
```

構文は以上のようにrtgライブラリを用いることで定義されています。
論文との相違点は、型τを省略している点、レコードを[]で、ヴァリアントを{[]}で表している点などがあります。
最後のq,mの定義はテスト用にあるだけなので消したいと思います。

```prolog
:- begin_var_names(['^[σlxktcbi]'],['^(true|bool|int)$']).
```

rtgライブラリには小文字のatomを変数に書き換えるマクロbegin_var_names/2およびend_var_names/1があります。
このライブラリを使うと正規表現を用いて小文字のアトムを変数に書き換えて論文により近い記述を可能にします。
ここでは、σlxktcbiから始まるアトムを変数とみなすと宣言しています。
第二パラメータではtrue,bool,intは含まないと指定しています。

```
% Kinding rules

K ⊢     t :: lσs  :- member(t::lσ2s,K), intersection(lσ2s,lσs,lσs).
_ ⊢  lσ2s :: lσs  :- intersection(lσ2s,lσs,lσs).
K ⊢     t ::{lσs} :- member(t::{lσ2s},K), intersection(lσ2s,lσs,lσs).
_ ⊢ {lσ2s}::{lσs} :- intersection(lσ2s,lσs,lσs).
_ ⊢     _ :: u.
```

カインド付けの規則はこのように定義できます。

```prolog
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
```

長いのですが、置換の規則は以上のように定義できます。
ここが長くなるのはドブランインデックス化されてないからだったりするのかもしれません。

```prolog
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
```

これは還元規則、評価するための規則です。
評価文脈なども使わずに素直にスモールステップ評価器として実装されていて繰り返し実行して変化がなくなれば終了です。

```prolog
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
```

自由型変数を求めるにはftv,kftvを用います。

```prolog
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

tftv(T,FTV),  \+member(t,FTV),  ([t::k|K],T) ▷ M : σ
--%------------------------------------------------------------ TABS
(K,T) ▷ λ(t::k,M) : ∀(t,k,σ).

(K,T) ▷ M : ∀(t,k,σ1),  K ⊢ σ2::k,  tsub([σ2/t],σ1,σ1_)
--%------------------------------------------------------------ TAPP
(K,T) ▷ (M ! σ2) : σ1_.

maplist({K,T}/[li=Mi,li:σi]>>((K,T) ▷ Mi : σi), lMs, lσs)
--%------------------------------------------------------------ RECORD
(K,T) ▷ lMs : lσs.

(K,T) ▷ M : σ1,   K ⊢ σ1::[l:σ2]
--%------------------------------------------------------------ DOT
(K,T) ▷ (M # l) : σ2.

(K,T) ▷ M1 : σ1,  (K,T) ▷ M2 : σ2,  K ⊢ σ1::[l:σ2]
--%------------------------------------------------------------ MODIFY
(K,T) ▷ modify(M1,l,M2) : σ1.

(K,T) ▷ M : σ1,  K ⊢ σ2::{[l:σ1]}
--%------------------------------------------------------------ VARIANT
(K,T) ▷ ({[l=M]}:σ2) : σ2.

(K,T) ▷ M : {lσs},
maplist({K,T,σ}/[li=Mi,li:σi]>>((K,T) ▷ Mi : (σi->σ)),lMs,lσs)
--%------------------------------------------------------------ CASE
(K,T) ▷ case(M,{lMs}) : σ.

:- end_var_names(_).
```

型システムは自然演繹スタイルで以上のように定義できていて、アルゴリズミックに評価できます。
このシステムは実に単純でとても簡単に実装できました。

## 2. テスト

それでは実行してみましょう。

```prolog:sostest.pl
:- expects_dialect(sicstus).
:- use_module(sos).
```

sicstus prolog的なモードにしてから、sos.plを読み込みます。

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
  test(m_xcb) :- m(1),m(true),m(xxx).
  test(m_λ) :- m(λ(x:t,x)).
  test(m_app) :- m(λ(x:t,x)$1).
  test(m_kapp) :- m(λ(x::u,x)!int).
  test(m_record) :- m([x=1,y=2]).
  test(m_record) :- m([x=1,y=2]#x).
  test(m_record) :- m(modify([x=1,y=2],x,2)).
  test(m_variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(m_variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
  
:- end_tests(avs).
```

構文チェックは以上のように使えます。

```prolog
:- begin_tests(q1).
  test(x) :- q(x).
  test(b) :- q(int).
  test(fun) :- q(int->int).
  test(empty_record):- q([]).
  test(one_element_record):- q([a:int]).
  test(three_elements_record):- q([a:int,b:int,c:bool]).
  test(nested_record):- q([a:int,b:[a:int,c:bool]]).
  test(variant):- q({[eint:int,eadd:['1':e,'2':e]]}).
:- end_tests(q1).
```

こちらは型のテストです。

```prolog
:- begin_tests(k).
  test(k):- k(u).
  test(k):- k([]).
  test(k):- k([l:int]).
  test(k):- k({[eint:int,eadd:['1':int,'2':int],emul:['1':int,'2':int]]}),!.
:- end_tests(k).
```

カインドのテスト

```prolog
:- begin_tests(q2).
  test(q):- q(∀(t,u,t)).
  test(q):- q(∀(t,[a:int,b:int],t)).
  test(q):- q(∀(t,{[a:t,b:t]},{[a:t,b:t,c:int]})),!.
  test(q):- q(∀(t,[a:t,b:t],[a:t,b:t,c:int])).
:- end_tests(q2).
```

多相的な型のテストです。

```prolog
:- begin_tests(msub).
  test(cb) :- msub([y/x],1,1),msub([y/x],true,true),msub([y/x],false,false).
  test(x) :- msub([y/x],x,y).
  test(x) :- msub([y/x,z/y],x,z).
  test(x) :- msub([z/y,y/x],x,z).
  test(x) :- msub([y/x,z/y],x,z).
  test(x) :- msub([z/y,y/x],x,z).
  test(λ) :- msub([y/x,z/y],λ(x:t,x),λ(x:t,x)).
  test(λ) :- msub([y/x,z/y],λ(a:t,x),λ(a:t,z)).
  test(λ) :- msub([z/y,y/x],λ(a:t,x),λ(a:t,z)).
/*
  todo:
  test(app) :- m(λ(x:t,x)$1).
  test(kapp) :- m(λ(x::u,x)$int).
  test(record) :- m([x=1,y=2]).
  test(record) :- m([x=1,y=2]#x).
  test(record) :- m(modify([x=1,y=2],x,2)).
  test(variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
*/
:- end_tests(msub).
```

置換テストはとちゅうでやめちゃいましたｗ

```prolog
:- begin_tests(eval).
  test(λ) :- λ(x:int,x) $ 1 ⟹* 1.
  test(λ) :- λ(t::u,λ(x:t,x)) ! int ⟹* λ(x:int,x).
  test(λ) :- λ(t::u,λ(x:t,x)) ! int $ 1 ⟹* 1.
  test(record) :- ([x=1,y=2]#x) ⟹* 1.
  test(record) :- ([x=1,y=2]#y) ⟹* 2.
  test(record) :- ([x=(λ(x:int,x)$1),y=2]#x) ⟹* 1.
  test(record) :- (modify([x=1,y=2],x,2)) ⟹* [x=2,y=2].
  test(record) :- (λ(z:int,[y=z])$10) ⟹* [y=10].
  test(record) :- (modify((λ(z:int,[x=1,y=z])$10),x,2)) ⟹* [x=2,y=10].  
  test(variant) :- ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}) ⟹* ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(variant) :- (case((λ(z:int,{[eint=z]}:{[eint:int,eadd:['1':int,'2':int]]})$1),{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})) ⟹* 1.
:- end_tests(eval).
```

評価は以上のように出来ます。

```prolog
:- begin_tests(typing).
  test(int) :- ([],[]) ▷ 10 : Q,!,Q=int.
  test(true) :- ([],[]) ▷ true : Q,!,Q=bool.
  test(false) :- ([],[]) ▷ false : Q,!,Q=bool.
  test(λ) :- ([],[]) ▷ λ(x:int,x) : Q,!,Q==(int->int).
  test(app) :- ([],[]) ▷ (λ(x:int,x)$1) : Q,!,Q=int.
  test(app) :- ([],[]) ▷ λ(t::u,λ(x:t,x))  : Q,!,Q= ∀(t,u,(t->t)).
  test(tapp) :- ([],[]) ▷ (λ(t::u,λ(x:t,x)) ! int) : Q,!,Q=(int->int).
  test(record) :- ([],[]) ▷ ([x=1,y=2]) : Q,!,Q=[x:int,y:int].
  test(record) :- ([],[]) ▷ ([x=1,y=2]#x) : Q,!,Q=int.
  test(record) :- ([],[]) ▷ ([x=1,y=2]#y) : Q,!,Q=int.
  test(record) :- ([],[]) ▷ ([x=(λ(x:int,x)$1),y=2]#x): Q, !,Q==int.
  test(record) :- ([],[]) ▷ (modify([x=1,y=2],x,2)) : Q,!,Q==[x:int,y:int] .
  test(record) :- ([],[]) ▷ (λ(z:int,[y=z])$10) : Q,!,Q==[y:int].
  test(record) :- ([],[]) ▷ (modify((λ(z:int,[x=1,y=z])$10),x,2)) : Q,!,Q==[x:int,y:int].
  test(variant) :- ([],[]) ▷ ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}) : Q,!, Q=={[eint:int,eadd:['1':int,'2':int]]}.
  test(variant) :- ([],[]) ▷ (case((λ(z:int,{[eint=z]}:{[eint:int]})$1),{[eint=λ(x:int,x)]})) : Q,!,Q==int.
  test(variant) :- ([],[]) ▷ (case((λ(z:int,{[eint=z]}:{[eint:int,b:int]})$1),{[eint=λ(x:int,x),b=λ(x:int,x)]})) : Q,!,Q==int.
:- end_tests(typing).
```

型検査は以上のように出来ます。

```prolog
:- run_tests.
:- halt.
```

最後にテストの実行はrun_testsで行い、haltで終了です。

## 参考文献

[^1]: A Polymorphic Record Calculus and Its Compilation
http://www.pllab.riec.tohoku.ac.jp/~ohori/research/toplas95.pdf
