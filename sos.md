# 2.1 Types, Kinds, and Kinded Substitutions

  The sets of types (ranged over by σ) and kinds (ranged over by k) are given by the following syntax:

    σ ::= b | t | σ→σ | {l:σ,···,l:σ} | <l:σ,···,l:σ> | ∀t::k.σ
    k ::= U | {{l:σ,···,l:σ}} | <<l:σ,···,l:σ>>

    where
      b stands for a given set of base types
      t for a given countably infinite set of type variables,
      l for a given set of labels,
      {l1:σ1,···,ln:σn} for record types,
      <l1:σ1,···,ln:σn> for variant types, and
      ∀t::k.σ for second-order types
        where
          type variable t is quantified over the set of types denoted by kind k.
      U is the universal kind denoting the set of all types.
      {{l1:σ1,···,ln:σn}} and <<l1:σ1,···,ln:σn>> are a record kind and a variant kind, respectively.
      The labels l1,···,ln appearing in a type or a kind must be pairwise distinct, and
      the order of their occurrence is insignificant.

  Syntax

    K ⊢ σ :: U   for any σ that is well formed under K
    K ⊢ t :: {{l1:σ1,...,ln:σn}}   if K(t) = {{l1:σ1,...,ln:σn,···}}
    K ⊢ {l1:σ1,...,ln:σn,···}::{{l1:σ1,...,ln:σn}}
      if {l1:σ1,...,ln:σn,···} is well formed under K
    K ⊢ t :: <<l1:σ1,...,ln:σn>>   if K(t) = <l1:σ1,...,ln:σn,···>
    K ⊢ <l1:σ1,...,ln:σn,···>::<<l1:σ1,...,ln:σn>>
      if <l1:σ1,...,ln:σn,···> is well formed under K

  Fig. 3. Kinding rules for the second-order calculus Λ∀,#.

# 2.2 Terms,Reduction,and Typing Rules

  The set of terms of Λ∀,# is given by the grammar:

    M ::= x | cb | λx:σ.M | M M | λt::k.M | M σ
        | {l=M,···,l=M} | M#l | modify(M,l,M)
        | (<l=M>:σ) | case M of <l=M,···,l=M>

  Grammer

    (β)        (λx:σ.M) N                           ⟹ [N/x] M
    (type-β)   (λt::k.M) σ                          ⟹ [σ/t] M
    (dot)      {l1=M1,···,ln=Mn}#li                 ⟹ Mi (1 ≤ i ≤ n)
    (modify)   modify({l1=M1,···,ln=Mn},li,N)       ⟹ {l1=M1,···,li=N,···,ln=Mn}
    (case)     case (<li=M>:σ) of <l1=M1,···,ln=Mn> ⟹ Mi M

  Fig. 4. The reduction rules for the second-order system Λ∀,#

    VAR     K,T ▷ x : σ    if T is well formed under K and T(x) = σ

    CONST   K,T ▷ cb : b   if T is well formed under K

            K,T{x:σ1} ▷ M1 : σ2
    ABS     ------------------------------
            K,T ▷ λx:σ1.M1 : σ1→σ2

            K,T ▷ M1 : σ1→σ2    K,T ▷ M2 : σ1
    APP     -------------------------------------
            K,T ▷ M1 M2 : σ2

            K{t::k},T ▷ M : σ
    TABS    ------------------------- if t ∉ FTV(T)
            K,T ▷ λt::k.M : ∀t::k.σ

            K,T ▷ M : ∀t::k.σ1    K ⊢ σ2::k
    TAPP    ----------------------------------
            K,T ▷ M σ2 :[σ2/t](σ1)

            K,T ▷ Mi : σi (1 ≤ i ≤ n)
    RECORD  --------------------------------------------
            K,T ▷ {l1=M1,···,ln=Mn} : {l1:σ1,···,ln:σn}

            K,T ▷ M : σ1    K ⊢ σ1::{{l:σ2}}
    DOT     ----------------------------------
            K,T ▷ M#l : σ2

            K,T ▷ M1 : σ1    K,T ▷ M2 : σ2    K ⊢ σ1::{{l:σ2}}
    MODIFY  -----------------------------------------------------
            K,T ▷ modify(M1,l,M2) : σ1

            K,T ▷ M : σ1    K ⊢ σ2::<<l:σ1>>
    VARIANT ----------------------------------
            K,T ▷ (<l=M>:σ2) : σ2

            K,T ▷ M : <l1:σ1,···,ln:σn>    K,T ▷ Mi : σi→σ (1 ≤ i ≤ n)
    CASE    -------------------------------------------------------------
            K,T ▷ case M of <l1=M1,···,ln=Mn> : σ

  Fig. 5. Type system of the second-order calculus Λ∀,#
