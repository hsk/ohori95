## 2.2

  我々のシステムでは型変数に依存することができるので、型の自由変数の概念を拡張する必要があります。
  `K` の下で well formed な型 `σ` に対して、 `EFTV(K,σ)` で示される、 `K` の下の `σ` の本質的に自由な変数の集合は、

  - `FTV(σ) ⊆ EFTV(K, σ)`.
  - `t ∈ EFTV(K, σ)` ならば `FTV(K(t)) ⊆ EFTV(K, σ)`.

  直感的には、`σ` が `K` によって指定された直接的または kind の制約 `t` を含む場合、`t ∈ EFTV(K, σ)` です。
  たとえば、`t1` は `{t1 :: U, t2 :: {{l:t1}}}` の `t2` では本質的に自由です。
  この概念は、当然、型を含む他の構文の構造にも及びます。
  型割り当て `T` は、有限集合の変数から型への写像です。
  `xi` から `σi` (1 ≤ i ≤ n) に束縛する代入型について、 `{x1:σ1,···,xn:σn}` と書きます。
  また、 `x ∉ dom(T)` を条件として、 `T ∪ {x:σ}` の `T{x:σ}` を書きます。
  型システムは、 `K,T ▷ M : σ` という形の型を導出する証明系として定義されます。
  タイピング規則のセットは図5に示されています。
  規則のタブ内で、条件 `t ∉ FTV(T)` は、`K {t::k}` の仮定の下で `t ∉ EFTV(K{t :: k}, T)` と等価です。
  我々は、 `K,T ▷ M : σ` がこの証明系で導出可能ならば、`Λ∀,# |- K, T ▷ M : σ` と書きます。

  サブタイプに基づくレコードの多型型規律とは異なり、この型は次のプロパティを持ちます。

# 3.4 Kinded Unification

  型推論アルゴリズムを開発するためには、 Robinson [1965] 単一化アルゴリズムを改良して、型変数にカインド制限を組み込む必要があります。

  カインド付き方程式の集合は、カインド割当て `K` と `E` が `K` の下で well formed な `E` の組からなる対 `(K, E)` です。
  すべての `(τ1, τ2) ∈ E` について `S(τ1) = S(τ2)` ならば、置換 `S` は `E` を満たすと言います。
  カインド付き置換 `(K1, S)` は、 `K` を尊重し、 `S` が `E` を満たす場合、カインド付き方程式 `(K, E)` の集合を単一化するものです。
  `(K1, E)` が `(K2, E)` のユニファイアーかつ `(K2, E)` の任意のユニファイア `(K3, S2)` で `(K3, S3)` は `K1` を、 `S2` は `S3 ◦ S` をそれぞれ示しているならば、 `(K1, E)` は `(K2, E)` の最も一般的なユニファイアです。

  我々は 変換により Gallier and Snyder [1989] のスタイルでカインド付き単一化アルゴリズム `U` を定義します。
  我々のシステムでは、各ルールは、型方程式の集合 `E`、カインド割当て `K`、置換 `S`、および（必ずしも整形式ではない）カインド割当て `SK` の `(E, K, S, SK)` の4タプルを変換します。
  これらのコンポーネントの意図される役割は次のとおりです: `E` は、一連の方程式を統一された状態に保ちます; `K` は検証されるカインドの制約を指定します; `S` は置換型として「解かれた」方程式を記録します; `SK` はすでに `S` に対して検証された「解決された」カインドの制約を記録します。

  ルールを指定する際に、我々は関数 `K`、 `SK`、および `S` をペアの集合として関数を扱います。
  我々はまた、次の表記を使用します。
  ラベルの有限集合から型への関数の範囲を `F` とします。

  `{F}` と `{{F}}` は、 `F` で識別されるレコード型とFで識別されるレコードカインドをそれぞれ表すように記述します。
  バリアント型とバリアントカインドでも同様の表記法が使用されます。
  2つの関数 `F1` と `F2` に対して、`dom(F) = dom(F1) ∪ dom(F2)` かつ、もし `l ∈ dom(F1)` ならば、 `F(l) = F1(l)` そうでなければ `F(l) = F2(l)` である関数Fについて、我々は `F1 ± F2` と書きます。
  図10に変換ルールの集合を示します。

  `(K, E)` を与えられたカインド付けされた方程式の集合とします。
  アルゴリズム U は、ルールが適用できなくなるまで、まずシステム `(E, K, ∅, ∅)` を `(E0, K0, S, SK)` に変換します。
  `E0 = ∅` ならば、対 `(K0, S)` を返し、それ以外の場合は失敗を報告します。
  次に、以下の定理があります。証明は付録を参照してください。

  **定理3.4.1.** アルゴリズムUは任意のカインド付けされた方程式の集合をとり、最も一般的な単一化器が存在すればそれを計算し、それ以外の場合は失敗を報告します。

  注意深い読者は、型変数を削除するときに、より強い「出現チェック」条件を必要とする可能性があることに気づいたかもしれません。
  例えば、ルール ii では、 `t∉FTV(τ)` の代わりに `t ∉ EFTV(K∪{(t, U)},τ)` を必要とする可能性があります。
  この強力な条件を要求することは、セクション2で述べた `{t1::{{l : t2}}, t2::{{l0 : t1}}}` のような "循環依存"を持つカインドの割り当てを禁止することに対応します。
  このアプローチをとらない背後の論理的根拠は、より強い条件が、置換が生成されるたびに非周期性の余分な検査のために単一化アルゴリズムの複雑さを増加させることです。
  単一化が繰り返し行われるため、型推論アルゴリズムが遅くなるでしょう。
  私たちのアプローチでは、`{t1 :: {{l : t1 → int}}}{x : t1} ¤ (x#l) x : int` のようないくつかの不要な開かれた項が許されていますが、問題は生じません。
  また、正規木 [Courcelle 1983] を使用して型システムを再帰型に拡張すると、それらの「再帰的な」カインドの割り当てを可能にすることが必要になります。
  Buneman and Ohori [1995] は、レコード多相を伴う再帰的プログラミングの可能性を論述しており、 Vasconcelos の最近の研究 [Vasconcelos 1994] は、我々のカインド付き単一化を無限正規木にまで拡張しています。

