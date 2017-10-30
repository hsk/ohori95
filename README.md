# スライド

  https://www.slideshare.net/bd_gfngfn/ss-80304969

# A Polymorphic Record Calculus and Its Compilation

  ATSUSHI OHORI

  Kyoto University

  ----

# 1. INTRODUCTION
# 1.1 Static Type System for Record Polymorphism

    fun move p = modify(p,X,p#X+1) : ∀t::{{X:int}}.t→t
    move({X=10,Y=0,Color="Red"}) : {X:int,Y:int,Color:string}
    fun transpose p = modify(modify(p,X,p#Y),Y,p#X)
      : ∀t1::U.∀t2::{{X:t1,Y:t1}}.t2→t2
    transpose({X=1.0,Y=10.0,Direction={Speed=30.0,Theta=1.0}})
      : {X:real,Y:real,Direction:{Speed:real,Theta:real}}
    fun dist p = case p of <Cartesian=λc.sqroot(square(c#X)+square(c#Y)),Polar=λp#R>
      : ∀t1::{{X:real, Y:real}}.∀t2::{{R:real}}.<Cartesian:t1,Polar:t2>→real
    dist(<Cartesian={X=0.0,Y=10.0,Color="Green"}>) : real

  Fig. 1. Example of programs with their inferred types.

# 1.2 Compilation Method for Record Polymorphism
# 1.3 Outline of the Development

        λlet,[]        (compile)     Λlet,#            (restrict)     Λ∀,#
    The implementation <-------- The explicit calculus <--------- The second-order
    calculus                          ^                           calculus
                                      | (type inference)
                                      |
                                     λlet,#
                                 The ML-style calculus

  Fig. 2. Relationship among the calculi.

    - val name = #Name;
    val name = fn : ’b#{Name:’a,...} -> ’a
    - fun name {Name=x,...} = x;
    val name = fn : ’b#{Name:’a,...} -> ’a

  Λ∀,# : The second-order calculus

  λlet,# : The ML-style calculus

  Λlet,# : The explicit calculus

  λlet,[] : The implementation calculus

# 2. POLYMORPHIC TYPE DISCIPLINE FOR RECORDS AND VARIANTS

  This section defines a second-order polymorphic record calculus, `Λ∀,#`, and proves its basic syntactic properties.

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

# 3. ML-STYLE TYPE INFERENCE SYSTEM
# 3.1 An ML-Style Polymorphic Record Calculus : λlet,#

    e ::= x | cb | λx.e | e e | let x=e in e
        | {l=e,···,l=e} | e#l | modify(e,l,e)
        | <l=e> | case e of <l=e,···,l=e>

    τ ::= t | b | τ→τ | {l:τ,···,l:τ} | <l:τ,···,l:τ>
    σ ::= τ | ∀t::k.σ
    k ::= U | {{l:τ,···,l:τ}} | <<l:τ,···,l:τ>>

  Syntax

    K ⊢ τ::U for any τ well formed under K
    K ⊢ t::{{l1:τ1,···,ln:τn}}    if K(t) = {{l1:τ1,···,ln:τn,···}}
    K ⊢ {l1:τ1,···,ln:τn,···}::{{l1:τ1,···,ln:τn}}
      if {l1:τ1,···,ln:τn,···} is well formed under K
    K ⊢ t:: <<l1:τ1,···,ln:τn>>   if K(t) = <l1:τ1,···,ln:τn,···>
    K ⊢ <l1:τ1,···,ln:τn,···>::<<l1:τ1,···,ln:τn>>
      if <l1:τ1,···,ln:τn,···> is well formed under K

  Fig. 6. Kinding rules for the ML-style type inference system λlet,#.

# 3.2 Operational Semantics of λlet,#

    VAR     K,T ▷ x : τ    if T is well formed under K and K ⊢ T (x) ≥ τ
    CONST   K,T ▷ cb : b   if T is well formed under K

            K,T ▷ e1 : τ1→τ2    K,T ▷ e2 : τ1
    APP     ------------------------------------
            K,T ▷ e1 e2 : τ2

            K,T{x:τ1} ▷ e1 : τ2
    ABS     ------------------------
            K,T ▷ λx.e1 : τ1→τ2

            K,T ▷ ei : τi (1 ≤ i ≤ n)
    RECORD  --------------------------------------------------
            K,T ▷ {l1=e1,···,ln=en} : {l1:τ1,···,ln:τn}

            K,T ▷ e : τ1    K ⊢ τ1::{{l:τ2}}
    DOT     ----------------------------------
            K,T ▷ e#l : τ2

            K,T ▷ e1 : τ1    K,T ▷ e2 : τ2    K ⊢ τ1::{{l:τ2}}
    MODIFY  -----------------------------------------------------
            K,T ▷ modify(e1,l,e2) : τ1

            K,T ▷ e : τ1    K ⊢ τ2::<<l : τ1>>
    VARIANT --------------------------------------------
            K,T ▷ <l=e> : τ2

            K,T ▷ e : <l1:τ1,···,ln:τn>    K,T ▷ ei : τi→τ (1 ≤ i ≤ n)
    CASE    -------------------------------------------------------------
            K,T ▷ case e of <l1=e1,···,ln=en> : τ

            K,T ▷ e : τ
    GEN     ------------------------------------ if Cls(K,T,τ) = (K',σ)
            K',T ▷ e : σ

            K,T ▷ e1 : σ    K,T{x:σ} ▷ e2 : τ
    LET     ------------------------------------
            K,T ▷ let x=e1 in e2 : τ

  Fig. 7. Typing rules for ML-style record calculus λlet,#.

    v    ::= cb | λx.e | {l=v,···,l=v} | <l=v>

    ev[] ::= [·] | ev[] e | v ev[] | let x=ev[] in e | {l1=v1,···,li−1=vi−1,li=ev[],···}
           | ev[]#l | modify(ev[],l,e) | modify(v,l,ev[]) | <l=ev[]> | case ev[] of <l=e,···,l=e>

    ev[(λx.e) v]                         ⟶ ev[[v/x]e]
    ev[{l1=v1,···,ln=vn}#li]             ⟶ ev[vi]
    ev[modify({l1=v1,···,ln=vn},li,v)]   ⟶ {l1=v1,···,li=v,···,ln=vn}
    ev[case <li=v> of <l1=e1,···,ln=en>] ⟶ ev[ei v]
    ev[let x = v in e]                   ⟶ ev[[v/x]e]

  Fig. 8. Call-by-value operational semantics of λlet,#.

# 3.3 Explicitly Typed Calculus Λlet,# Corresponding to λlet,#

    M ::= (x τ···τ) | cb | λx:τ.M | M M | Poly(M:σ) | let x:σ = M in M
        | {l=M,···,l=M} | M:τ#l | modify(M:τ,l,M)
        | (<l=M>:τ) | case M of <l=M,···,l=M>

  Syntax

    VAR     K,T {x:∀t1::k1···∀tn::kn.τ0} ▷ (x τ1···τn) :[τ1/t1,···,τn/tn](τ0)
              if T{x:∀t1::k1···∀tn::kn.τ0} is well formed under K
              and (K,[τ1/t1,···,τn/tn]) respects K{t1::k1,···,tn::kn}

    CONST   K,T ▷ cb : b if T is well formed under K

            K,T ▷ M1 : τ1→τ2    K,T ▷ M2 : τ1
    APP     --------------------------------------
            K,T ▷ M1 M2 : τ2

            K,T{x:τ1} ▷ M1 : τ2
    ABS     -----------------------------
            K,T ▷ λx:τ1.M1 : τ1→τ2

            K,T ▷ Mi : τi (1 ≤ i ≤ n)
    RECORD  ------------------------------------------------
            K,T ▷ {l1=M1,···,ln=Mn} : {l1:τ1,···,ln:τn}

            K,T ▷ M : τ1    K ⊢ τ1::{{l:τ2}}
    DOT     ---------------------------------------
            K,T ▷ M:τ1#l : τ2

            K,T ▷ M1 : τ1    K,T ▷ M2 : τ2    K ⊢ τ1::{{l:τ2}}
    MODIFY  ---------------------------------------------------------
            K,T ▷ modify(M1:τ1,l,M2) : τ1

            K,T ▷ M : τ1    K ⊢ τ2::<<l:τ1>>
    VARIANT ----------------------------------
            K,T ▷ (<l=M>:τ2) : τ2

            K,T ▷ M : <l1:τ1,···,ln:τn>    K,T ▷ Mi : τi→τ (1 ≤ i ≤ n)
    CASE    ----------------------------------------------------------------
            K,T ▷ case M of <l1=M1,···,ln=Mn> : τ

            K,T ▷ M : τ
    GEN     -------------------------- if Cls(K,T,τ) = (K',σ)
            K',T ▷ Poly(M:σ) : σ

            K,T ▷ M1 : σ    K,T{x:σ} ▷ M2 : τ
    LET     ------------------------------------------
            K,T ▷ let x:σ = M1 in M2 : τ

  Fig. 9. Typing rules for the explicitly typed record calculus Λlet,#.

# 3.4 Kinded Unification

    (i)     (E ∪ {(τ,τ)},K,S,SK) ⟹ (E,K,S,SK)

    (ii)    (E ∪ {(t,τ)},K ∪ {(t,U)},S,SK) ⟹
            ([τ/t](E),[τ/t](K),[τ/t](S) ∪ {(t,τ)},[τ/t](SK) ∪ {(t,U)}) if t ∉ FTV(τ)

    (iii)   (E ∪ {(t1,t2)},K ∪ {(t1,{{F1}}),(t2,{{F2}})},S,SK) ⟹
            ([t2/t1](E ∪ {(F1(l),F2(l))|l ∈ dom(F1) ∩ dom(F2)}),
             [t2/t1](K) ∪ {(t2,[t2/t1]({{F1 ± F2}}))},
             [t2/t1](S) ∪ {(t1,t2)},[t2/t1](SK) ∪ {(t1,{{F1}})})

    (iv)    (E ∪ {(t1,{F2})},K ∪ {(t1,{{F1}})},S,SK) ⟹
            ([{F2}/t1](E ∪ {(F1(l),F2(l))|l ∈ dom(F1)}),[{F2}/t1](K),
             [{F2}/t1](S) ∪ {(t1,{F2})},[{F2}/t1](SK) ∪ {(t1,{{F1}})})
            if dom(F1) ⊆ dom(F2) and t ∉ FTV({F2})

    (v)     (E ∪ {({F1},{F2})},K,S,SK) ⟹ (E ∪ {(F1(l),F2(l))|l ∈ dom(F1)},K,S,SK)
            if dom(F1) = dom(F2)

    (vi)    (E ∪ {(t1,t2)},K ∪ {(t1,<<F1>>),(t2,<<F2>>)},S,SK) ⟹
            ([t2/t1](E ∪ {(F1(l),F2(l))|l ∈ dom(F1) ∩ dom(F2)}),
             [t2/t1](K) ∪ {(t2,[t2/t1](<<F1 ± F2>>))},
             [t2/t1](S) ∪ {(t1,t2)},[t2/t1](SK) ∪ {(t1,<<F1>>)})

    (vii)   (E ∪ {(t1,<F2>)},K ∪ {(t1,<<F1>>)},S,SK) ⟹
            ([<F2>/t1](E ∪ {(F1(l),F2(l))|l ∈ dom(F1)}),[<F2>/t1](K),
             [<F2>/t1](S) ∪ {(t1,<F2>)},[<F2>/t1](SK) ∪ {(t1,<<F1>>)})
            if dom(F1) ⊆ dom(F2) and t1 ∉ FTV(<F2>)

    (viii)  (E ∪ {(<F1>,<F2>)},K,S,SK) ⟹ (E ∪ {(F1(l),F2(l))|l ∈ dom(F1)},K,S,SK)
            if dom(F1) = dom(F2)

    (ix)    (E ∪ {(τ11→τ21,τ12→τ22)},K,S,SK) ⟹ (E ∪ {(τ11,τ12),(τ21,τ22)},K,S,SK)

    For a notation of the form X ∪ Y appeared in the left hand side of each rule,we assume that X and Y are disjoint.

  Fig. 10. Transformation rules for kinded unification

# 3.5 The Type Inference Algorithm

    erase((x τ1···τn))       = x
    erase(λx:τ.M1)           = λx.erase(M1)
    erase(M1:τ#l)            = erase(M1)#l
    erase(modify(M1:τ,l,M2)) = modify(erase(M1),l,erase(M2))
    erase((<l=M1>:τ))        = <l=erase(M1)>
    erase(Poly(M1:σ))        = erase(M1)
    erase(let x:σ=M1 in M2)  = let x=erase(M1) in erase(M2)

    WK(K,T,x) = if x ∉ dom(T) then failure
                else let ∀t1::k1...∀tn::kn.τ = T(x),
                         S=[s1/t1,···,sn/tn] (s1,···,sn are fresh)
                     in (K{s1::S(k1),···,sn::S(kn)},∅,(x s1···sn),S(τ))

    WK(K,T,λx.e1) = let (K1,S1,M1,τ1) = WK(K{t::U},T{x:t},e1) (t fresh)
                    in (K1,S1,λx:S1(t).M1,S1(t)→τ1).

    WK(K,T,e1 e2) = let (K1,S1,M1,τ1) = WK(K,T,e1)
                        (K2,S2,M2,τ2) = WK(K1,S1(T),e2)
                        (K3,S3) = U(K2,{(S2(τ1),τ2→t)}) (t fresh)
                    in (K3,S3◦S2◦S1,(S3◦S2(M1) S3(M2)),S3(t)).

    WK(K,T,{l1=e1,···,ln=en}) =
      let (K1,S1,M1,τ1) = WK(K,T,e1)
          (Ki,Si,Mi,τi) = WK(Ki−1,Si−1◦···◦S1(T),ei) (2 ≤ i ≤ n)
      in (Kn,Sn◦···◦S2◦S1,
          {l1=Sn◦···◦S2(M1),···,li=Sn◦···◦Si+1(Mi),···,ln=Mn},
          {l1:Sn◦···◦S2(τ1),···,li:Sn◦···◦Si+1(τi),···,ln:τn})

    WK(K,T,e1#l) = let (K1,S1,M1,τ1) = WK(K,T,e1)
                       (K2,S2) = U(K1{t1::U,t2::{{l:t1}}},{(t2,τ1)}) (t1,t2 fresh)
                   in (K2,S2◦S1,S2(M1):S2(t2)#l,S2(t1)).

    WK(K,T,modify(e1,l,e2)) =
      let (K1,S1,M1,τ1) = WK(K,T,e1)
          (K2,S2,M2,τ2) = WK(K1,S1(T),e2)
          (K3,S3) = U(K2{t1::U,t2::{{l:t1}}},{(t1,τ2),(t2,S2(τ1))}) (t1,t2 fresh)
      in (K3,S3◦S2◦S1,modify(S3◦S2(M1):S3(t2),l,S3(M2)),S3(t2)).

    WK(K,T,case e0 of <l1=e1,···,ln=en>) =
      let (K0,S0,M0,τ0) = WK(K,T,e0)
          (Ki,Si,Mi,τi) = WK(Ki−1,Si−1◦···◦S0(T),ei) (1 ≤ i ≤ n)
          (Kn+1,Sn+1) =U(Kn{t0::U,···,tn::U},{(Sn◦···S1(τ0),<l1:t1,···,ln:tn>)}
                        ∪{(Sn◦···Si+1(τi),ti→t0)|1 ≤ i ≤ n}) (t0,···,tn fresh)
      in (Kn+1,Sn+1◦···◦S0,
          (case Sn+1◦···◦S1(M0) of <···,li=Sn+1◦···◦Si+1(Mi),···>),Sn+1(t0))

    WK(K,T,<l=e1>) = let (K1,S1,M1,τ1) = WK(K,T,e1)
                     in (K1{t::<<l:τ1>>},S1,(<l=M1>:t),t) (t fresh)

    WK(K,T,let x=e1 in e2) = let (K1,S1,M1,τ1) = WK(K,T,e1)
                                 (K1',σ1) = Cls(K1,S1(T),τ1)
                                 (K2,S2,M2,τ2) = WK(K1',(S1(T)){x:σ1},e2)
                             in (K2,S2◦S1,let x:S2(σ1)=Poly(S2(M1:σ1)) in M2,τ2)

  Fig. 11. Type inference algorithm

# 4. COMPILATION

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


# 4.2 The Type System of λlet,[]

    τ ::= t | cb | τ→τ | {l:τ,···,l:τ} | <l:τ,···,l:τ> | idx(l,τ) ⇒ τ
    σ ::= τ | ∀t::k.σ

  where `idx(l, τ1) ⇒ τ2` denotes functions that take an index value denoted by `idx(l, τ1)` and yield a value of type `τ2`.
  Since index values are not first-class objects, it is not necessary to included index types `idx(l, τ)` as separate types.
  The set of kinds and the kinding rules are the same as those of `λlet,#`.

  ここで `idx（l、τ1）⇒τ2`は` idx（l、τ1） 'で示されるインデックス値をとり、 `τ2`型の値をとる関数を表す。
  インデックス値はファーストクラスのオブジェクトではないので、別々の型としてインデックス型 `idx（l、τ）`を含める必要はありません。
  種類と罰則は `λlet、＃ 'のものと同じです。

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
    (iapp)    (λI.C) Ï                 ⟹ [Ï/I]C
    (let)     let x=C1 in C2            ⟹ [C1/x]C2

  Fig. 14. The reduction rules for the implementation calculus λlet,[].

# 4.3 Compilation Algorithm

    IdxSet(t::U) = ∅
    IdxSet(t::{{F}}) = {idx (l, t)|l ∈ dom(F)}
    IdxSet(t::<<F>>) = {idx (l, t)|l ∈ dom(F)}

    IdxSet(∀t1::k1···tn::kn.τ) = IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)
    IdxSet(K) = ∪{IdxSet(t::k)|(t::k) ∈ K}


    C(L,T,(x τ1···τn)) = let (∀t1::k1 ···tn::kn.idx(l1,t1') ⇒···idx(lm,tm') ⇒ τ) = T(x)
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
             = (∀t1::k1···∀tn::kn.τ1)∗
          C1 = C(L{I1:idx(l1,t1'),···,In:idx(lm,tm')},T,M1) (I1,···,Im fresh)
      in λI1···λIm.C1
    C(L,T,let x:σ=M1 in M2) = let C1 = C(L,T,M1)
                                  C2 = C(L,T {x:(σ)∗},M2)
                              in let x=C1 in C2

  Fig. 15. Compilation algorithm.

# 4.4 Eliminating Vacuous Type Variables from λlet,# Typing
# 4.5 Correctness of Compilation
# 5. IMPLEMENTATION
# 5.1 Extension to Standard ML

    (* simple examples *)
    - fun moveX point = #> point => {x = #x point + 1};
    val moveX = fn : ’a#{x:int,...} -> ’a#{x:int,...}
    - moveX {x=1,y=2};
    val it = {x=2,y=2} : {x:int,y:int}
    - moveX {x=1, y=2, z=3, color="Green"};
    val it = {color="Green",x=2,y=2,z=3} : {color:string,x:int,y:int,z:int}

    (* database like examples *)
    - fun wealthy {Salary =s,...} = s > 100000;
    val wealthy = fn : ’a#{Salary:int,...} -> bool
    - fun young x = #Age x < 24;
    val young = fn : ’a#{Age:int,...} -> bool
    - fun youngAndWealthy x = wealthy x andalso young x;
    val youngAndWealthy = fn : ’a#{Age:int,Salary:int,...} -> bool
    - fun select display l pred =
          fold (fn (x,y) => if pred x then (display x)::y else y) l nil;
    val select = fn : (’a -> ’b) -> ’a list -> (’a -> bool) -> ’b list
    - fun youngAndWealthyEmployees l = select #Name l youngAndWealthy;
    val youngAndWealthyEmployees = fn
         : ’b#{Age:int,Name:’a,Salary:int,...} list -> ’a list

  Fig. 16. Interactive programming session in SML#.

# 5.2 Implementation Strategies
# 6. CONCLUSIONS
# APPENDIX
# PROOFS OF MAJOR THEOREMS
# ACKNOWLEDGMENTS
# REFERENCES
