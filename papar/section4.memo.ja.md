# 3.3 Explicitly Typed Calculus Λlet,# Corresponding to λlet,#

    M ::= (x τ···τ) | cb | λx:τ.M | M M | Poly(M:σ) | let x:σ = M in M
        | {l=M,···,l=M} | M:τ#l | modify(M:τ,l,M)
        | (<l=M>:τ) | case M of <l=M,···,l=M>

  Syntax

<!--27 868-->

# 4. コンパイル

  この章では、 ML スタイルの多相レコード計算 `λlet,#` を以下に定義された実装計算 `λlet,[]` にコンパイルするアルゴリズムを開発します。

<!--26 869-->

    V ::= cb | λx.C | {V,···,V} | <Ï=V> | λI.C' (for some C' such that C'↓C').

    EV[] ::= [·] | EV[] C | V EV[] | let x=EV[] in C | {V,···,V,EV[],···} | EV[][Ï]
           | modify(EV[],I,C) | modify(V,Ï,EV[]) | <Ï=EV[]> | switch EV[] of C,···,C
           | EV[] Ï | λI.EV[]

    EV[(λx.C) V]                                 ⟶ EV[[V/x]C]
    EV[{V1,···,Vn}[i]]                           ⟶ EV[Vi]
    EV[modify({V1,···,Vi−1,Vi,Vi+1,···,Vn},i,V)] ⟶ EV[{V1,···,Vi−1,V,Vi+1,···,Vn}]
    EV[switch <i=V> of C1,···,Cn]                ⟶ EV[Ci V]
    EV[(λI.C') Ï]                                ⟶ EV[[Ï/I]C] if C'↓C'
    EV[let x=V in C]                             ⟶ EV[[V/x]C]

  図12. λlet,[] のコールバイバリュー評価オペレーションセマンティクス

## 4.1 実装計算: λlet,[]

  我々は、直接インデックス付け可能なベクターと整数タグの `switch` 文を使用して実装計算を定義し、多相レコード計算の効率的な抽象マシンとして定義します。

  後述するように、インデックス値は、後で定義するコンパイルアルゴリズムによって常に静的に計算され、ファーストクラスの値として扱う必要はありません。
  そこで、次の新しいインデックスのカテゴリ (`Ï` の範囲) を導入し、それらを特別に扱います:

    Ï ::= I | i
    ここで、
      I は与えられたインデックス変数の集合を表し、
      i は自然数を表します。

  λlet,[] (`C` の範囲) の raw 項の集合は次の構文で与えられます:

    C ::= x | c b |λx.C | C C | let x=C in C | {C,···,C} | C[Ï]
        | modify(C,Ï,C) | <Ï=C> | switch C of C,···,C | λI.C | C Ï
    ここで
      {C1,···,Cn} はレコードのベクター表現です。
      C[Ï] はベクター C からインデックス値 Ï の要素を検索するインデックス式、
      switch C of C1,···,Cn は、バリアント C の整数タグを解析し、
                               対応する関数 Ci を C の値に適用します。
      λI.C はインデックス抽象で; そして
      C Ï はインデックス関数適用です。

  `λlet,#` のように、 call-by-value の操作的意味は、評価コンテキスト（`EV[]` の範囲）、値の集合（`V` の範囲）、および call-by-value コンテキスト書き換え `EV[C1]−→EV[C2]` の形式の公理を用いて定義されます。
  `C = EV[C1]1`、`EV[C1]1 -EV→EV[C2]1` となるような `EV[]1`、`C1`、`C2`が存在するならば、我々は１ステップで `C` は `C'` に評価されるといい、`C −EV→ C'`と書きます。
  我々は、 `-EV→` の反射的推移的閉包について `-EV→→` と書き; `C -EV→→C'` ならば `C↓C'` かつ `C' -EV→C''` で `C''` は現れません; いくつかの `C'` に対して `C↓C'` ならば `C↓` と書きます。
  図12は、値の集合、 call-by-value の評価コンテキスト、および λlet,[] のコンテキスト書き換え公理の集合の相互再帰的定義を与えます。

<!--27 870-->

## 4.2 λlet,[] の型システム

  次の節で定義されたコンパイルアルゴリズムの正当性を確立するために、実装計算の型システムを定義します。

  実装計算でラベル付けされたレコードとラベル付きバリアントを表すために、ラベルの集合の全体の順序 `<<` を仮定し、レコード型 `{l1:τ1,···,ln:τn}` またはそのバリアント型 `<l1:τ1,···,ln:τn>` は `l1<<···<<ln` の条件を満たす必要があります。
  `<<` の通常の選択は、ラベルの文字列表現における辞書順です。
  `τ` が上記の形式のいずれかである場合、`τ` のラベル `li` のインデックスを `i` と定義します。
  上記レコード型のレコード項は、 `i` 番目の要素が `li` フィールドであるベクターです。
  上記のバリアント型の `li` バリアントは、 `j` 番目の要素が `lj` 変形の関数に対応する関数のベクターを含む `switch` 文によって操作される整数 `i` でタグ付けされた値です。
  たとえば、レコード型が `int` 型の `Age` フィールドと `string` 型の `Name` フィールドで構成されている場合は、`{Age:int,Name:string}` の形式である必要があります。したがって、このレコード型の `Name` のインデックスは `2` です。
  この型の可能な項は、 λlet,# の `{Name="Joe",Age=21}` に対応する `{21,"Joe"}` を含みます。
  同様に、実数型の `Dollar` と実数型の `Pound` のバリアント型は、 `<Dollar:real,Pound:real>` の形式でなければなりません。したがって、型の `Pound` のインデックスは `2` です。
  この型の `switch` 文は、`Dollar` と `Pound` の関数のベクターからこの順番で構成され、この型の `100.0` の `Pound` バリアントは `<2=100.0>` と表され、これは、λlet,＃ における上記型の `<Pound=100.0>` の (単相) 項に対応します。

  多相演算を説明するために、インデックス値に対して新しい形式の `idx(l,τ)` を導入します。
  `τ` がレコード型またはバリアント型の場合、この型は `τ` の `l` のインデックスを示します。
  我々は `idx(l,τ)` で示されるインデックス値に対して `|idx(l,τ)|` と書きます。
  たとえば、`|idx(Name,{Age:int,Name:string})| = 2` です。
  `τ` が型変数 `t` であるとき、 `idx(l,t)` は、 `t` のインスタンス化に応じて可能なインデックス値を示し、 `|idx(l,t)|` 定義されていません。

  実装計算の型の集合は、次の構文で与えられます。

    τ ::= t | cb | τ→τ | {l:τ,···,l:τ} | <l:τ,···,l:τ> | idx(l,τ) ⇒ τ
    σ ::= τ | ∀t::k.σ

  ここで、 `idx(l,τ1)⇒τ2` は、 `idx(l,τ1)` で表されるインデックス値を取り、 `τ2` 型の値を生成する関数を示します。
  インデックス値はファーストクラスのオブジェクトではないので、別々の型としてインデックス型 `idx(l,τ)` を含める必要はありません。
  kind の集合と kinding 規則は λlet,# と同じです。

  この計算の型システムは、以下の形式の判断のための証明システムとして定義されています。

    K,L,T ▷ C : τ       typing judgment
    L |- I : idx(l,τ)    index judgment

  ここで、 `K` は kind 割り当てであり、 `T` は前の計算での型割り当てです。
  `L` はインデックス割り当てであり、インデックス変数のセットから `idx(l,τ)` という形式のインデックス型へのマッピングです。
  `FTV(τ) ⊆ dom(K)` の場合、 `τ,τ'` に現れるすべての型の `idx(l,τ')` に対して、 レコード kind または `K` の下で `l` フィールドを含むバリアント kind を持つならば、型 `τ` は `K` の下で well formed です.
  `τ` が `K{t1::k1···tn::kn}` の下で well formed ならば、型 `∀t1::k1···tn::kn.τ` は `K` の下で　well formed です。
  `L` 内の各型が `K` 下で well formed ならば、 `L` は `K` の下で well formed です。
  `T` 内の各型が `K` の下で well formed ならば、型割り当て `T` は `K` の下で well formed です。

<!--28 871-->

  Syntax

    K,L,T ▷ C : τ       typing judgment
    L ⊢ Ï : idx(l,τ)   index judgment

    IVAR      L{I:idx(l,τ)} ⊢ I : idx(l,τ)
    ICONST1   L ⊢ i : idx(li,{l1:τ1,···,ln:τn})    1 ≤ i ≤ n
    ICONST2   L ⊢ i : idx(li,<l1:τ1,···,ln:τn>)    1 ≤ i ≤ n

    VAR       K,L,T{x:σ} ▷ x : τ      if T{x:σ} and L are well formed under K and K ⊢ σ ≥ τ
    CONST     K,L,T ▷ cb : b          if T and L are well formed under K

              K,L,T ▷ C1 : τ1→τ2    K,L,T ▷ C2 : τ1
    APP       ----------------------------------------
              K,L,T ▷ C1 C2 : τ2

              K,L,T{x:τ1} ▷ C1 : τ2
    ABS       -----------------------
              K,L,T ▷ λx.C1 : τ1→τ2

              K,L{I:idx(l,τ1)},T ▷ C1 : τ2
    IABS      --------------------------------
              K,L,T ▷ λI.C1 : idx(l,τ1) ⇒ τ2

              K,L,T ▷ C : idx(l,τ1) ⇒ τ2    L ⊢ Ï : idx(l,τ1)
    IAPP      ---------------------------------------------------
              K,L,T ▷ C Ï : τ2

              K,L,T ▷ Ci : τi (1 ≤ i ≤ n)
    RECORD    ----------------------------------------
              K,L,T ▷ {C1,···,Cn} : {l1:τ1,···,ln:τn}

              K,L,T ▷ C1 : τ1    K ⊢ τ1::{{l:τ2}}    L ⊢ Ï : idx(l,τ1)
    INDEX     ------------------------------------------------------------
              K,L,T ▷ C1[Ï] : τ2

              K,L,T ▷ C1 : τ1    K ⊢ τ1::{{l:τ2}}    L ⊢ Ï : idx(l,τ1)    K,L,T ▷ C2 : τ2
    MODIFY    --------------------------------------------------------------------------------
              K,L,T ▷ modify(C1,Ï,C2) : τ1

              K,L,T ▷ C : τ1    K ⊢ τ2::<<l:τ1>>    L ⊢ Ï : idx(l,τ2)
    VARIANT   -----------------------------------------------------------
              K,L,T ▷ <Ï=C> : τ2

              K,L,T ▷ C : <l1:τ1,···,ln:τn>    K,L,T ▷ Ci : τi→τ (1 ≤ i ≤ n)
    SWITCH    -----------------------------------------------------------------
              K,L,T ▷ switch C of C1,···,Cn : τ

              K{t1::k1···tn::kn},L,T ▷ C : τ
    GEN       ----------------------------------- if ti ∉ FTV(L ∪ T) (1 ≤ i ≤ n)
              K,L,T ▷ C : ∀t1::kn···tn::kn.τ

              K,L,T ▷ C1 : σ    K,L,T{x:σ} ▷ C2 : τ
    LET       -----------------------------------------
              K,L,T ▷ let x=C1 in C2 : τ

  図13. 実装の計算のための型付け規則 λlet,[].

  型付け規則の集合は図13に示されています。
  我々は λlet,[] の型推論には関心がないので、我々が λlet,# に使用したものよりも GEN に対してより一般的でより自然な規則を採用します。
  これにより、主題簡約特性の証明がやや容易になります。
  このようなシステムでは、 `K,L,T ▷ C : σ` が導出されれば、 `λlet,[] |- K,L,T ▷ C : σ` と書きます。
  `λlet,[] |- K,L,T ▷ C : σ` ならば `σ` が `K` の下で well formed であることは容易に証明されます。

<!--29 872-->

    (β)       (λx.C1) C2                ⟹ [C2/x]C1
    (index)   {C1,···,Cn}[i]            ⟹ Ci (1 ≤ i ≤ n)
    (modify)  modify({C1,···,Cn},i,C)   ⟹ {C1,···,Ci−1,C,Ci+1,···,Cn} (1 ≤ i ≤ n)
    (switch)  switch <i=C> of C1,···,Cn ⟹ Ci C (1 ≤ i ≤ n)
    (iapp)    (λI.C) Ï                  ⟹ [Ï/I]C
    (let)     let x=C1 in C2            ⟹ [C1/x]C2

  図14. 実装計算 λlet,[] の簡約規則.

  この型システムの、 主題簡約特性を示します。これは、後でコンパイルアルゴリズムが λlet,# の操作上の動作を保持することを確認するのに役立ちます。
  λlet,[] の使用法は λlet,# を実装するための抽象マシンであるので、 λlet,[] 自体の型の健全性のより強い性質は必要ありません。
  λlet,# のコンパイルされた項の操作的意味論に関する λlet,[] の型の健全性は、後で確立するコンパイルの正当性に従います。

  λlet,[] の簡約公理を図14に示します。
  `C1` から `C2` への簡約公理の1つを適用することによって、 `C1` から `C2` が得られた場合、 `C1→C2` と書かれます。
  簡約関係 `C1→→C2` は `→` の再帰的推移閉包として定義されます。
  以下の置換補題は、主題簡約定理を証明するのに有用です。

## 4.3 コンパイルアルゴリズム

  型推論によって得られた型情報を用いて λlet,# のコンパイルアルゴリズムを開発します。
  型推論アルゴリズムは、与えられた λlet,# 項を、コンパイルに必要なすべての型情報を含む明示的に型指定された Λlet,#  に変換しています。
  そこで、 Λlet,# 項を λlet,[] にコンパイルするアルゴリズムとしてコンパイルアルゴリズムを示します。

  はじめに説明したように、多相レコード操作を含む多相関数をコンパイルするための戦略は、適切なインデックス抽象を挿入することです。
  この戦略では、 λlet,# の型 `σ` の多相関数を、 `σ` の kind 型限定子によって示される必要なインデックス抽象を挿入することによって `σ` から得られる型を持つ項にコンパイルします。
  ソースコードの型とコンパイルされたコードの型との間の形式的な関係を確立するために、まず以下の補助的な概念を定義します。

  kind `k` の `t` に含まれるインデックス型の集合 `IdxSet(t::k)` は、以下のように定義されます。

    IdxSet(t::U) = ∅
    IdxSet(t::{{F}}) = {idx(l,t)|l ∈ dom(F)}
    IdxSet(t::<<F>>) = {idx(l,t)|l ∈ dom(F)}

  この定義は、多相型と kind 割り当てに拡張されています:

    IdxSet(∀t1::k1···tn::kn.τ) = IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)
    IdxSet(K) = ∪{IdxSet(t::k)|(t::k) ∈ K}

  λlet,# で与えられた型 `σ` について、 λlet,[] の対応する型 `(σ)*` は以下のように定義され

    (∀t1::k1···tn::kn.τ)* = ∀t1::k1···tn::kn.idx(l1,t1')⇒···idx(lm,tm')⇒τ

`idx(l1,t1'),···,idx(lm,tm')` は次のように順序付けられた `IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)` のインデックス型の集合です:
`i < j` または `i = j` かつ `l << l'` ならば、 `idx(l,ti)`は `idx(l',tj)` に先行します。
特に、任意の単相型 `τ` について、`(τ)* = τ` です。
  以下はその例です。

    (∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.t2→t3)* =
      ∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.idx(a,t2)⇒idx(b,t2)⇒idx(a,t3)⇒t2→t3

  この定義は、次のように型の割り当てに拡張されます:

    (T)* = {x : (T(x))* |x ∈ dom(T)}

  kind 割り当て `K` に対して、 `K` によって決定されるインデックス割り当て `LK` を `LK = {I : idx(l,t)|idx(l,t) ∈ IdxSet(K),each I fresh}` として定義します。

<!--31 874-->

  コンパイルアルゴリズムは、図15において、 `LK,(T)*` および `M` をとり、実装計算の項を計算するアルゴリズム `C` として与えられます。
  `LK` は任意の対 `(l,t)` に対して多くても1つの `(I,idx(l,t)) ∈ LK` があるという性質を持っているので、 したがって、 `C` は決定論的アルゴリズムです。

<!--32 875-->



    C(L,T,(x τ1···τn)) = let (∀t1::k1···tn::kn.idx(l1,t1')⇒···idx(lm,tm')⇒τ) = T(x)
                             S = [τ1/t1,···,τn/tn]
                             Ïi = | i if |idx(l,S(ti'))| = i
                                  | I if |idx(l,S(ti'))| is undefined and (I:idx(l,S(ti'))) ∈ L
                         in (x Ï1···Ïm)
    C(L,T,cb) = cb
    C(L,T,λx:τ.M) = λx.C(L,T{x:τ},M)
    C(L,T,M1 M2) = C(L,T,M1) C(L,T,M2)
    C(L,T,{l1=M1,···,ln=Mn}) = {C(L,T,M1),···,C(L,T,Mn)}
    C(L,T,M:τ#l) = let C = C(L,T,M) and
                       Ï = | i if |idx(l,τ)| = i
                           | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                   in C[Ï]
    C(L,T,modify(M1:τ,l,M2)) = let C1 = C(L,T,M1),
                                   C2 = C(L,T,M2),and
                                   Ï = | i if |idx(l,τ)| = i
                                       | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                               in modify(C1,Ï,C2)
    C(L,T,(<l=M>:τ)) = let C = C(L,T,M) and
                           Ï = | i if |idx(l,τ)| = i
                               | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                       in <Ï=C>
    C(L,T,case M of <l1=M1,···,ln=Mn>) =
      switch C(L,T,M) of C(L,T,M1),···,C(L,T,Mn)
    C(L,T,Poly(M1:∀t1::k1···∀tn::kn.τ1)) =
      let ∀t1::k1···∀tn::kn.idx(l1,ti') ⇒ idx(lm,tm') ⇒ τ1
             = (∀t1::k1···∀tn::kn.τ1)*
          C1 = C(L{I1:idx(l1,t1'),···,In:idx(lm,tm')},T,M1) (I1,···,Im fresh)
      in λI1···λIm.C1
    C(L,T,let x:σ=M1 in M2) = let C1 = C(L,T,M1)
                                  C2 = C(L,T {x:(σ)*},M2)
                              in let x=C1 in C2

  図15. コンパイルアルゴリズム

<!--33 876-->

## 4.4 λlet,# 型付けから空の型変数を削除

  上記のアルゴリズムは kind 付き型付き Λlet,# をkind 付き型付き λlet,[] に変換します。
  これを λlet,# のコンパイルアルゴリズムとして使用するには、注意が必要な微妙な点が1つあります。
  それは、一貫性 (coherence) の問題です [Breazu-Tannen et al. 1991]。
  Ohori [1989] に示されているように、 ML の Damas-Milner システムは Core XML に関して一貫性がなく、 λlet,# と Λlet,# との関係にも同じことが当てはまります。
  （関連する議論については Harper and Mitchell [1993] も参照）。

  一貫性の失敗の原因は、型付けにおける結果の型または型の割り当てに現れない型の導出で使用される自由型の変数です。
  これらの型変数はまた、前節で開発したコンパイルアルゴリズムを適用する際に問題を引き起こします。
  これを見るには、 raw の項 `(λx.cb) (λx.(x#l) + 1)` を考えてみましょう。

  型推論アルゴリズムは、以下の型の λlet,＃

    {t::{{l : int}}},∅ ▷ (λx.cb) (λx.(x#l) + 1) : b

  に対して以下の型の Λlet,＃ を生成します:

    {t::{{l : int}}},∅ ▷ (λx:t → int.cb) (λx:t.(x#l) + 1) : b

  kind 付き型変数 `t` は、多相フィールド選択 `x#l` の型検査に導入されますが、型代入または結果型には現れないため、これ以上インスタンス化されることはありません。
  結果として、与えられた閉じた項は、決定されない `l` の位置を示す空きインデックス変数を含む Λlet,# の開いた項に変換されます。

  この問題に対する我々の解は、3章で与えられたミルナー型の推論アルゴリズムを改良して、これらの "冗長(redundant)" 型または空の型変数を削除することです。
  `K,T ▷ e : τ` の型変数 `t` は、`t ∈ dom(K)` かつ `t ∈/ EFTV(K,τ) ∪ EFTV(K,T)` ならば空になります。

  あらかじめ定義された基本型 `b0` があると仮定します。
  `b0` の選択は重要ではありません。
  `K,T ▷ e : τ` を型付けし、　`t`　を　`t　∈/ FTV(K(t))` のような型付けの空の型変数とします。
  そして `K` は `K'{t::k}` と書かれます。
  次のようにして、`K` の `t` の正規化インスタンス `τt` を定義します:

          b0    if k = U
    τt =  {F}   if k = {{F}}
          <F>   if k = <<F>>

  我々は、kind 付き置換 `(K',[τt/t])` を適用することによって、型付けから `t` を削除することができます。
  空型変数の集合が `K` に相互循環依存性を持たない場合、 `1 ≤ i ≤ j ≤ n` ならば、 `ti ∈/ FTV(K(tj))` となるような 列 `t1,···,tn` を持ちます。
  そして、`t1,···,tn` について上記のプロセスを繰り返すことにより、 kind 付き置換のシーケンス `(Ki,[τti/ti])` を得ます。
  我々は、kind 付き置換 `(Kn,[τn/tn] ◦···◦ [τi/t1])` として、 `K,T ▷ e : τ` の正規化インスタンス化を定義します。
  この定義から、以下の結果を容易に証明することができます。

#### 系4.4.2

  `λlet,# |- K,T ▷ e : τ` かつ `(K0,S0)` が `K,T ▷ e : τ` の正規化インスタンス化ならば、`λlet,# |- K0,T ▷ e : τ` です。

  これは、空の型変数集合に循環依存性がない場合、その項の型付けの性質に影響を与えることなくそれらを削除できることを示しています。
  我々は `K0,T ▷ e : τ` を `λlet,# |- K,T ▷ e : τ` の正規化インスタンスと呼びます。

  我々は λlet,# のプログラムを、以下の形式の閉じた型として識別します:

    ∅,∅ ▷ e : σ

  前の章で定義された型推論アルゴリズムを改良して、トップレベルの型抽象化の直前に推論された型付けが存在する場合にはそれを正規化インスタンスにします; それ以外の場合は、型エラーが報告されます。
  プログラムは閉じた型付けを有さなければならず、その派生には循環依存性を持つ kind 割り当てが含まれていないため、このプロセスはプログラムの型付け性を変更しません。
  上記の形式のプログラムから、洗練された型推論アルゴリズムは、
  λlet,# の上記形式のプログラムから、洗練された型推論アルゴリズムは、以下の閉じた型付け Λlet,＃ を生成します

    ∅,∅,∅ ▷ Poly(M:σ) : σ

  我々は、これらの閉じた型付けを別々のコンパイルの単位とみなします。

  この改良により、前の節で与えられたコンパイルアルゴリズムは、 λlet,# のコンパイルアルゴリズムとして機能します。
  系4.3.2 は次のようになります。

#### 系4.4.3

  もし `e` が well typed な λlet,# プログラムならば、 `λlet,# |- ∅,∅ ▷ e : σ`、 `Λlet,# |- ∅,∅ ▷ M : σ` および `C(∅,∅,M)` が `λlet,[] |- ∅,∅,∅ ▷ C : (σ)∗` のような `C` で成功する、いくつかの `S,M,σ` について、`WK(∅,∅,e)` が `(∅,S,M,σ)`で成功します。

  コンパイルの例を見てみましょう。
  λlet,# の項 `λx.x#Name` から、型推論プロセスは次のプログラムを生成します

    Λlet,# |- ∅,∅ ▷ Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)
                  : ∀t1::U.∀t2::{{Name:t1}}.t2→t1

  このプログラムから、コンパイルアルゴリズムは次の結果を生成します

  C(∅,∅,Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)) = λI.λx.x[I]

  これには以下の型付けがあります:

    λlet,[] |- ∅,∅,∅ ▷ λI.λx.x[I] : ∀t1::U.∀t2::{{Name:t1}}.idx(Name,t2) ⇒ t2→t1

  プログラム

    let name=λx.x# Name in (name {Name="Joe",Office=403},
                            name {Name="Hanako",Age=21,Phone=7222})

  は、前の章で見たように Λlet,# で次のプログラムに変換されます:

    E ≡ let name:∀t1::U.∀t2::{{Name:t1}}.t2→t1
              = Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)
        in ((name string {Name:string,Office:string})
              {Name="Joe",Office=403},
              (name string {Name:string,Age:int,Phone:int})
              {Name="Hanako",Age=21,Phone=7222})

<!--35 878-->

  コンパイルアルゴリズムは次の結果を生成し

    C(∅,∅,E) = let name=λI.λx.x[I] in (name 1 {"Joe",403},
                                        name 2 {21,"Hanako",7222})

  期待される型付けを有し、`("Joe","Hanako")` と評価されます。

  次は、多相バリアントと空型変数削除を含むプログラムの例です。
  以下の λlet,# のプログラム

    let point = <Cartesian={X=2.0,Y=3.0}> in
      case point of <Cartesian=λc.sqroot(square(c#X) + square(c#Y)),Polar=λp#R>

  は、 Λlet,＃ の次のプログラムに変換されます。

    F ≡ let point:∀t::<<Cartesian:{X:real,Y:real}>>.t
            = Poly((<Cartesian={X=2.0,Y=3.0}>:t)
                    : ∀t::<<Cartesian:{X:real,Y:real}>>.t)
        in case (point <Cartesian:{X:real,Y:real},Polar:{R:b0}>) of
           <Cartesian=λc:{X:real,Y:real}.sqroot(square(c#X)+square(c#Y)),
            Polar=λp:{R:b0}.x#R>

  これから、コンパイルアルゴリズムは次のコードを生成します:

    C(∅,∅,F) = let point=λI.<I={2.0,3.0}>
                 in switch (point 1) of <λc.sqroot(square(c[1]) + square(c[2])),λx.x[1]>

  `case`　文の `Polar` 分岐に対しては、空型変数の削除が正しく実行され、未使用のフィールド拡張 `x#R` は、デフォルトのインデックス値　`1`　でインデックス式にコンパイルされます。

## 4.5 コンパイルの正当性

  4節では、コンパイルアルゴリズムが型付けを保持することを示しました。
  この章では、コンパイルアルゴリズムがプログラムの操作上の動作も保持することを示しています。
  λlet,# の型システムは、その操作的意味論に関しては健全であることを示しているので、操作上の振る舞いを保持することで、 λlet,# の型システムはコンパイルされた λlet,[] 内のコードの操作的意味論に関しても健全です。

  基本型の項に関して、所望の性質は、元の項とコンパイルされた項が同じ定数値に評価されるという単純なものです。
  我々はこれを多相型を含む任意の型に一般化する必要があります。
  我々の戦略は、上記の関係を任意の型に持ち上げる論理的な関係という概念を適用することです。

  `σ` を閉じた型 λlet,# とします。
  `σ` を集合 `{e|λlet,# |- ∅,∅ ▷ e : σ}` とし、 `Termσ` を集合 `{M|λlet,[] |- ∅,∅,∅ ▷ M : (σ)*}` とします。
  我々は、以下のように、 `σ` 上の誘導によって、型インデックス付きの関係の集合 `{Rσ ⊆ termσ × Termσ}` を定義します。

    (e,C) ∈ R σ ⇐⇒ (1) e ↓ iff C ↓ and
                      (2) one of the following conditions holds

  — `σ = b` のとき、 `e ↓ e'` かつ `C ↓ C'` ならば `e' = C'` です。

  - `σ = τ1→τ2` のとき、任意の `e0`、 `C0` に対して、`(e0,C0) ∈ Rτ1`、 `(e e0,C C0) ∈ Rτ2` です。

  - もし `σ = {l1:τ1,···,ln:τn}` のとき、`e ↓ e'` かつ `C ↓ C'` ならば、`1 ≤ i ≤ n` であるすべての`(ei,Ci) ∈ Rτi` で `e' = {l1=e1,···,ln=en}`、 `C' = {C1,···,Cn}` です。

<!--36 879-->

  - `σ = <l1:τ1,···,ln:τn>` のとき、`e ↓ e'` かつ `C ↓ C'` ならば、`e' = <li= e''>`、 `C' = <i=C''>` かつ `(e'',C'') ∈ Rτi` であるような `i` が存在します。

  - `σ = ∀t1::k1.···tn::kn.τ` のとき

    (σ)* = ∀t1::k1.···tn::kn.idx(l1,t1') ⇒···idx(lm,tm')⇒τ

  ならば、 `{t1::k1.···tn::kn}` を満たす任意の基礎置換 `S` に対して、

    (e,(···(C i1)···im)) ∈ R^(S(τ))

  であり、ここで `ij = |S(idx(lj,tj'))| (1≤ j ≤ m)` です。

  ここで、 λlet,# の型健全性定理（定理3.2.1）と λlet,[] の主題定理（定理4.2.3）から、 `e ∈ termσ` かつ `C ∈ Termσ` かつ `e ↓ e'` かつ `C ↓ C'` ならば `e' ∈ termσ` かつ `C' ∈ Termσ` です。
  さらに、 `Rσ` の定義によって、`(e,C）∈ Rσ` ならば `(e',C') ∈ Rσ` です。

  `T` を λlet,# の閉じた型割当てとします。
  λlet,# における `T`-環境は、任意の `x ∈ dom(η1)`、`η1(x) ∈ term^(T(x))` で `dom(η1) = dom(T)` となるような関数 `η1` です。
  λlet,[] における `A(T)*`-環境は、任意の `x∈dom(η2), η2(x) ∈ Term ^((T)* (x))`で、`dom(η2) = dom(T)` となるような関数 `η2` です。
  `L` を well-formed な閉じた型インデックス割り当てとします。
  λlet,[] における `A(T)*`-環境 `η2`は、すべての `I ∈ dom(L)` に対して、その `I` の値を `|L(I)|` とすることによって `dom（T）∪dom（L）`上で定義された関数に一意に拡張されます。 
  我々は、 `η2` の `dom(L)` 拡張について `ηL2` と書きます。

  関係 `R` は環境に拡張されます。
  `RT` は λlet,# の `T`-環境と λlet,[] の `T`-環境との関係であり、任意の `x ∈ dom(T), (η1(x),η2(x)) ∈ R^(T(x))` に対して、 `(η1,η2) ∈ RT` です。

  今、次の定理があり、その証明は付録に引き継がれます。

#### 定理4.5.1

  `Λlet,# |- K,T ▷ M : σ` は任意の型付けとします。
  もし、`C(LK,(T)∗,M) = C` ならば、 `K` を考慮した任意の基礎置換 `S` かつ任意の対の環境`(η1,η2) ∈ R^(S(T)), (η1(erase(M)),η2_{S(LK)} (C)) ∈ R^(S(σ))` です。

  プログラムには、以下の性質があります。

#### 系4.5.2

  `e` が well typed な λlet,# プログラムならば、`C(∅,∅,M)` が `(e,C) ∈ Rσ` のようないくつかの `S` で成功する、いくつかの `S,M,σ` について、`WK(∅,∅,e)` が `(∅,S,M,σ)`で成功します。

  観測可能な型の集合を以下の構文で定義すると

    ω ::= b | {l:ω,···,l:ω} | <l:ω,···,l:ω>

  関係 `Rω` は本質的に同一的（レコードとヴァリアントのモジュロ表現）であるため、 λlet,# とそのコンパイルされた項の観測可能な型のプログラムは、本質的に同じ値に評価されます。