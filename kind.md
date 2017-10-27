### Lemma 3.1.1.

  If K |- σ1 ≥ σ2 and K |- σ2 ≥ σ3 then K |- σ1 ≥ σ3.

Let T and τ be well formed under K.
The closure of τ under T, K, denoted by Cls(K, T, τ), is a pair (K0, ∀t1::k1···∀tn::kn.τ) such that K0{t1::k1,···,tn::kn} = K and {t1,···,tn} = E FTV (K, τ) \ E FTV(K,T).
Note that if λ let, # |- K, T ¤ e : τ and Cls(K, T, τ) = (K0, σ) then T and σ are well formed under K0.
A type assignment is a mapping from a finite set of variables to polytypes.
The set of typing rules for λ let, # is given in Figure 7.

# 3.4 Kinded Unification

In order to develop a type inference algorithm, we need to refine Robinson’s [1965] unification algorithm to incorporate kind constraints on type variables.

A kinded set of equations is a pair (K, E) consisting of a kind assignment K and a set E of pairs of types such that E is well formed under K.
We say that a substitution S satisfies E if S(τ1) = S(τ2) for all (τ1, τ2) ∈ E.
A kinded substitution (K1, S) is a unifier of a kinded set of equations (K, E) if it respects K and if S satisfies E.
(K1, S) is a most general unifier of (K2, E) if it is a unifier of (K2, E) and if for any unifier (K3, S2) of (K2, E) there is some substitution S3 such that (K3, S3) respects K1 and S2 = S3 ◦ S.

We define a kinded unification algorithm `U` in the style of Gallier and Snyder [1989] by transformation.
In our system each rule transforms a 4-tuple of the form (E, K, S, SK) consisting of a set E of type equations, a kind assignment K, a substitution S, and a (not necessarily well-formed) kind assignment SK.
Intended roles of these components are: E keeps the set of equations to be unified; K specifies kind constrains to be verified; S records “solved” equations as a form of substitution; and SK records “solved” kind constraints that has already been verified for S.

In specifying rules, we treat functions K, SK, and S as sets of pairs.
We also use the following notations.
Let F range over functions from a finite set of labels to types.
We write {F} and {{F}} to denote the record type identified by F and the record kind identified by F, respectively.
Similar notations are used for variant types and variant kinds.
For two functions F1 and F2 we write F1 ± F2 for the function F such that dom(F) = dom(F1) ∪ dom(F2) and such that for l ∈ dom(F), F(l) = F1(l) if l ∈ dom(F1); otherwise F(l) = F2(l).
Figure 10 gives the set of transformation rules.

Let (K, E) be a given kinded set of equations.
The algorithm U first transforms the system (E, K, ∅, ∅) to (E0, K0, S, SK) until no more rules can apply.
It then returns the pair(K0, S) if E0 = ∅; otherwise it reports failure.
We then have the following theorem, whose proof is deferred to the Appendix.

**Theorem 3.4.1.** The algorithm U takes any kinded set of equations, computes a most general unifier if one exists, and reports failure otherwise.

The careful reader may have noticed that we could have required a stronger “occur check” condition when eliminating a type variable.
For example, in the rule ii, we could have required `t ∉ E FTV(K ∪ {(t, U)}, τ)` instead of `t ∉ FTV(τ)`.
Requiring this stronger condition corresponds to disallowing kind assignments having “cyclic dependencies” such as `{t1::{{l : t2}}, t2::{{l0 : t1}}}` we have mentioned in Section 2.
The rationale behind not taking this approach is that the stronger condition would increase the complexity of the unification algorithm due to the extra check of acyclicity every time a substitution is generated.
Since unification is repeatedly performed, this would slow down the type inference algorithm. Although our approach allows some useless open terms, such as `{t1 ::{{l : t1 → int}}}{x : t1} ¤ (x#l) x : int`, the typability on closed terms does not change and therefore does not create any problems.
Also, if we extend the type system to recursive types using regular trees [Courcelle 1983], allowing those “cyclic” kind assignments would become essential.
Buneman and Ohori [1995] discusse possible usefulness of recursive programming with record polymorphism, and Vasconcelos’ recent work [Vasconcelos 1994] extends our kinded unification to infinite regular trees.

