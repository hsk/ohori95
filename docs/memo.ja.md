# Prologで実装した多相レコード計算

## 要約

Ohoriによる多相レコード計算をPrologにより実装しました。
できるだけ論文に忠実に作ることを目的としています。

## はじめに

- 1. sos.pl Λ∀# Second-Order System
- 2. mss.pl λlet# Ml-Style type inerence System
- 3. tmss.pl Λlet# Typed Ml-Style System
- 4. ics.pl λlet[] Implementation Calculs System
- 5. compiler.pl λlet[] へのコンパイラ

プログラムは大きく分けて、sos.pl,mss.pl,tmss.pl,ics.pl,compiler.plに分かれています。
sos.plにはsostest.plが対応しています。
sosはSecond Order Systemの略で、多相レコード計算の極めて単純なシステムです。
このプログラムは他のプログラムとは独立してみることが出来ます。

mss は ML スタイルの型推論システムであり ML スタイルの多相レコード計算です。
tmss は ML スタイルの型推論システムが推論したあとの型がついたMLスタイルの多相レコード計算です。
ics は ML スタイルの型推論システムをコンパイルしたあとのシステムです。
compiler.pl は tmss から ics へのコンパイラです。

## 1. Second-Order System Λ∀,# の実装

まずは演算子の優先順位定義と、rtgモジュール読み込み、マクロ定義があります。
rtgモジュールは構文定義をBNF風の記述を可能にするライブラリです。

```prolog
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

型システムは自然演繹スタイルで以上のように定義できて、アルゴリズミックに評価できます。
このシステムは実に単純でとても簡単に実装できました。


## 2. mss は ML スタイルの型推論システムであり ML スタイルの多相レコード計算です。

## 3. tmss

## 4. ics は実装計算システムの略です。

多相レコード計算のための効率的なコンパイル方法を確立するために、まず、実装計算を定義します。
ここで、レコードは、直接索引付けによって要素にアクセスするベクターとして表され、バリアントは、スイッチステートメント内の関数のベクター内の位置を示す自然数でタグ付けされた値として表されます。

ics.pl は実装計算のみを持つことにします。

## 5. mss から ics へのコンパイラ

次に、型推論アルゴリズムによって得られた型情報を用いて、多相レコード計算を実装計算に変換するアルゴリズムを開発します。
コンパイルアルゴリズムの正確性が証明されています。
つまり、コンパイルアルゴリズムは、プログラムの入力と操作の両方の動作を保持するために示されています。

プログラムは記号が多用されており、小文字も変数として用いたいのでマクロによって小文字の本来は変数ではないアトムの値を変数に置き換えています。

C がコンパイルのアルゴリズムだと。
