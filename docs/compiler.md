# 3.3 Explicitly Typed Calculus Λlet,# Corresponding to λlet,#

コンパイル元の言語はMなので型付きの言語からのコンパイルをする

    M ::= (x τ···τ) | cb | λx:τ.M | M M | Poly(M:σ) | let x:σ = M in M
        | {l=M,···,l=M} | M:τ#l | modify(M:τ,l,M)
        | (<l=M>:τ) | case M of <l=M,···,l=M>

  Syntax

# 4.3 Compilation Algorithm

    IdxSet(t::U) = ∅
    IdxSet(t::{{F}}) = {idx(l,t)|l ∈ dom(F)}
    IdxSet(t::<<F>>) = {idx(l,t)|l ∈ dom(F)}

の３つがインデックス集合を求める関数で方のカインドがレコードおよびヴァリアント型ならばFのドメインlに対してidx(l,t)がある。
フィールドに対してインデックス関数があるわけだな。

    IdxSet(∀t1::k1···tn::kn.τ) = IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)
    IdxSet(K) = ∪{IdxSet(t::k)|(t::k) ∈ K}

この２つは多相型についてのインデックスセットはそれぞれを足し合わせたものである。
カインド集合Kについてのインデックスセットはそれぞれをやはり足し合わせたものである。

    C(L,T,(x τ1···τn)) = let (∀t1::k1 ···tn::kn.idx(l1,t1') ⇒···idx(lm,tm') ⇒ τ) = T(x)
                             S = [τ1/t1,···,τn/tn]
                             Ïi = | i if |idx(l,S(ti'))| = i
                                   | I if |idx(l,S(ti'))| is undefined and (I:idx(l,S(ti'))) ∈ L
                         in (x Ï1···Ïm)

これは、instantiation 具体化の式のコンパイルだ

    C(L,T,cb) = cb

cbはそのままだ

    C(L,T,λx:τ.M) = λx.C(L,T{x:τ},M)

関数は、xはそのままに、型をTに加えてMをコンパイルするだけである。

    C(L,T,M1 M2) = C(L,T,M1) C(L,T,M2)

関数適用はそれぞれの項をコンパイルするだけ

    C(L,T,{l1=M1,···,ln=Mn}) = {C(L,T,M1),···,C(L,T,Mn)}

レコードもそれぞれの項をコンパイルするだけ

    C(L,T,M:τ#l) = let C = C(L,T,M) and
                       Ï = | i if |idx(l,τ)| = i
                            | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                   in C[Ï]

レコードのフィールド参照はMをコンパイルしたCのインデックスを取り出すlet式にコンパイルかな。インデックスÏはidx(l,τ)がiならiでそうでなければidx(l,τ)が定義されていればundefinedで (I:idx(l,τ)) ∈ L なら Iであると。
τからidxの集合がもとめるのでそれを元に計算できるってことかな。

    C(L,T,modify(M1:τ,l,M2)) = let C1 = C(L,T,M1),
                                   C2 = C(L,T,M2),and
                                   Ï = | i if |idx(l,τ)| = i
                                        | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                               in modify(C1,Ï,C2)
レコードの更新も同じ

    C(L,T,(<l=M>:τ)) = let C = C(L,T,M) and
                           Ï = | i if |idx(l,τ)| = i
                                | I if |idx(l,τ)| is undefined and (I:idx(l,τ)) ∈ L
                       in <Ï=C>
    C(L,T,case M of <l1=M1,···,ln=Mn>) =
      switch C(L,T,M) of C(L,T,M1),···,C(L,T,Mn)
ヴァリアントは後回し
    C(L,T,Poly(M1:∀t1::k1···∀tn::kn.τ1)) =
      let ∀t1::k1···∀tn::kn.idx(l1,ti') ⇒ idx(lm,tm') ⇒ τ1
             = (∀t1::k1···∀tn::kn.τ1)∗
          C1 = C(L{I1:idx(l1,t1'),···,In:idx(lm,tm')},T,M1) (I1,···,Im fresh)
      in λI1···λIm.C1
これは、一般化、generarizationの式なので多相的な事をした時の話
    C(L,T,let x:σ=M1 in M2) = let C1 = C(L,T,M1)
                                  C2 = C(L,T {x:(σ)∗},M2)
                              in let x=C1 in C2
これはlet式

  Fig. 15. Compilation algorithm.


コンパイルアルゴリズムは１１つの規則からなる


# 4.4 Eliminating Vacuous Type Variables from λlet,# Typing
# 4.5 Correctness of Compilation
