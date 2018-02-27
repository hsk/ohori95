# 4. COMPILATION
# 4.1 Implementation Calculus : λlet,[]

    Ï ::= I | i
    where
      I stands for a given set of index variables and
      i for natural numbers.
    C ::= x | cb |λx.C | C C | let x=C in C | {C,···,C} | C[Ï]
        | modify(C,Ï,C) | <Ï=C> | switch C of C,···,C | λI.C | C Ï

    where
      {C1,···,Cn} is a vector representation of a record;
      C[I] is index expression retrieving the element of index value I from vector C;
      switch C of C1,···,Cn analyzes the integer tag of a variant C and
                            applies the corresponding function C i to the value of C;
      λI.C is index abstraction; and
      C I is index application.

  Syntax

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

  Fig. 12. Call-by-value evaluation operational semantics of λlet,[].

# 4.2 The Type System of λlet,[]

    τ ::= t | cb | τ→τ | {l:τ,···,l:τ} | <l:τ,···,l:τ> | idx(l,τ) ⇒ τ
    σ ::= τ | ∀t::k.σ

  where `idx(l,τ1)⇒τ2` denotes functions that take an index value denoted by `idx(l,τ1)` and yield a value of type `τ2`.
  Since index values are not first-class objects, it is not necessary to included index types `idx(l,τ)` as separate types.
  The set of kinds and the kinding rules are the same as those of `λlet,#`.

  ここで `idx(l,τ1)⇒τ2` は `idx(l,τ1)` で示されるインデックス値をとり、 `τ2` 型の値をとる関数を表す。
  インデックス値はファーストクラスのオブジェクトではないので、別々の型としてインデックス型 `idx（l、τ）`を含める必要はありません。
  カインドとカインド付け規則は `λlet、＃` のものと同じです。

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

  Fig. 13. Typing rules for the implementation calculus λlet,[].


    (β)       (λx.C1) C2                ⟹ [C2/x]C1
    (index)   {C1,···,Cn}[i]            ⟹ Ci (1 ≤ i ≤ n)
    (modify)  modify({C1,···,Cn},i,C)   ⟹ {C1,···,Ci−1,C,Ci+1,···,Cn} (1 ≤ i ≤ n)
    (switch)  switch <i=C> of C1,···,Cn ⟹ Ci C (1 ≤ i ≤ n)
    (iapp)    (λI.C) Ï                  ⟹ [Ï/I]C
    (let)     let x=C1 in C2            ⟹ [C1/x]C2

  Fig. 14. The reduction rules for the implementation calculus λlet,[].

