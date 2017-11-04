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
