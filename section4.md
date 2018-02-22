# A Polymorphic Record Calculus and Its Compilation

  ATSUSHI OHORI
  
  Kyoto University

  The motivation of this work is to provide a type-theoretical basis for developing a practical polymorphic programming language with labeled records and labeled variants.
  Our goal is to establish both a polymorphic type discipline and an efficient compilation method for a calculus with those labeled data structures.
  We define a second-order, polymorphic record calculus as an extension of Girard-Reynolds polymorphic lambda calculus.
  We then develop an ML-style type inference algorithm for a predicative subset of the second-order record calculus.
  The soundness of the type system and the completeness of the type inference algorithm are shown.
  These results extend Milner’s type inference algorithm, Damas and Milner’s account of ML’s let polymorphism, and Harper and Mitchell’s analysis on XML.
  To establish an efficient compilation method for the polymorphic record calculus, we first define an implementation calculus, where records are represented as vectors whose elements are accessed by direct indexing, and variants are represented as values tagged with a natural number indicating the position in the vector of functions in a switch statement.
  We then develop an algorithm to translate the polymorphic record calculus into the implementation calculus using type information obtained by the type inference algorithm.
  The correctness of the compilation algorithm is proved; that is, the compilation algorithm is shown to preserve both typing and the operational behavior of a program.
  Based on these results, Standard ML has been extended with labeled records, and its compiler has been implemented.

  Categories and Subject Descriptors: D.3.1 [Programming Languages]: Formal Definitions and Theory; D.3.2 [Programming Languages]: Language Classifications—applicative languages; D.3.3 [Programming Languages]: Language Constructs and Features—data types and structures

  General Terms: Languages

  Additional Key Words and Phrases: Compilation, polymorphism, record calculus, type inference, type theory

  ----

  A preliminary summary of some of the results of this article appeared in Proceedings of ACM Symposium on Principles of Programming Languages, 1992, under the title “A compilation method for ML-style polymorphic record calculi.”

  This work was partly supported by the Japanese Ministry of Education under scientific research grant no. 06680319.

  Author’s address: Research Institute for Mathematical Sciences, Kyoto University, Sakyo-ku, Kyoto 606-01, JAPAN; email: ohori@kurims.kyoto-u.ac.jp

  Permission to copy without fee all or part of this material is granted provided that the copies are not made or distributed for direct commercial advantage, the ACM copyright notice and the title of the publication and its date appear, and notice is given that copying is by permission of ACM.
  To copy otherwise, or to republish, requires a fee and/or specific permission.

  c 1999 ACM 0164-0925/99/0100-0111 $00.75

  ----

# 1. INTRODUCTION

  Labeled records and labeled variants are widely used data structures and are essential building blocks in various data-intensive applications such as database programming.
  Despite their practical importance, however, existing polymorphic programming languages do not properly support these data structures.
  Standard ML [Milner et al. 1990] contains labeled records and a form of labeled variants, but their allowable operations are restricted to monomorphic ones.
  For example, consider the following simple function name on records:

  <!--2-->

    name ≡ λx.x#Name

  where x#Name is our syntax for selecting the Name field from record x.
  This function is polymorphic in the sense that it can be applied to terms of any record type containing a Name field, such as {Name : string, Age : int} or {Name : string, Office : int}.
  One way of writing this function in ML is

    fun name(x) = #Name x

  where #Name is an ML’s syntax for λx.x#Name.
  This program is rejected by the current ML compiler, unless the programmer explicitly specifies the type of x that restricts the possible argument values to be those records that have a fixed set of labels, as in:

    fun name(x:{Name:string, Age:int}) = #Name x

  Unfortunately, writing such a type specification is not only cumbersome but also eliminates most of the flexibility of functions operating on records like name above.
  An analogous situation exists for labeled variants.
  We use variant types (disjoint union types) when we want to treat values of different types uniformly.
  A significant advantage of labeled variants over simple disjoint union types is that they support flexible programming by designating the kind of a value by a symbolic label.
  For example, consider a variant value payment defined as:

    payment ≡ <Pound=100.0>

  where value 100.0 is tagged with variant label Pound.
  payment can be treated as a value of various different variant types such as <Pound : real, Dollar : real> or <Pound : real, Yen : int> or any other variant types containing a Pound : real field.
  Unfortunately, this form of flexible programming is unavailable in existing polymorphic languages since they restrict variant values to be monomorphic.
  In Standard ML, for example, a variant type may be defined as:

    datatype PoundOrYen = Pound of real | Yen of int

  But this definition ties the variant labels Pound and Yen to this particular type PoundOrYen.
  As a consequence, if a value such as payment is defined for this type, it cannot be used as a value of other variant types.
  In Standard ML programming, a commonly adopted ad hoc strategy used to get around this problem is to define a variant type containing all the possible components and to omit some of the cases when manipulating variant values.
  This approach, however, introduces runtime exceptions of “match failure,” many of which are essentially type errors that should have been caught at compile time.

  It is highly desirable to extend a polymorphic programming language to allow polymorphic manipulation of labeled records and labeled variants.
  In this article, we use the term record polymorphism to refer to the form of polymorphism required for polymorphic manipulation of both labeled records and labeled variants.
  Our goal is to provide a basis to develop a polymorphic programming language that supports record polymorphism.
  There are two technical challenges in achieving this goal.
  The first is the development of a static type system that can represent record polymorphism.
  The second is the development of an efficient compilation method for polymorphic operations on records and variants.
  In this article, we provide solutions to the two problems.
  In the rest of this section, we shall explain the problems and outline the solutions presented in this article.
  Part of this article is based on a preliminary presentation of kinded abstraction and type-inference-based compilation [Ohori 1992].

  <!--3-->

# 1.1 Static Type System for Record Polymorphism

  Record polymorphism is based on the property that labeled-field access is polymorphic and can therefore be applied to any labeled data structure containing the specified field.
  For example, the function name, which accesses the `Name` field in a record, and the value `payment`, which accesses the `Pound` branch in a case statement, have all the types of the forms:

    name : {Name:τ,···}→τ,
    payment : <Pound:real,···>

  However, conventional polymorphic type systems cannot represent the set of all possible types of those shapes and therefore cannot represent the polymorphic nature of programs containing those terms.

  Cardelli [1988] observed that this form of polymorphism can be captured by defining a subtyping relation and allowing a value to have all its supertypes.
  This approach also supports certain aspects of method inheritance and provides a type-theoretical basis for object-oriented programming.
  Cardelli and Wegner [1985] extended this approach to a second-order type system.
  Type inference systems with subtyping have also been developed [Fuh and Mishra 1988; Mitchell 1984; Stansifer 1988].
  It is, however, not clear whether or not the mechanism for record polymorphism should be coupled with a strong mechanism of subtyping.
  In the presence of subtyping, a static type no longer represents the exact record structure of a runtime value.
  For example, a term

    if true then {A = 1, B = true} else {B=false, C=”Cat”}

  has a type `{B:bool}`, but its runtime value would presumably be `{A=1,B=true}`.
  This property may be problematic when we want to deal with those operations, such as equality test, that depend on the exact structure of values.
  As we shall discuss in Section 6, subtyping also complicates implementation.
  An alternative approach, initiated by Wand [1987; 1988], is to extend ML-style polymorphic typing directly to record polymorphism.
  This idea was further developed in a number of type inference systems [Jategaonkar and Mitchell 1993; Ohori and Buneman 1988; 1989; Rémy1989; 1992; 1994b; Wand 1989].

  In these type systems, a most general polymorphic type scheme can be inferred for any typable untyped term containing operations on records.
  By appropriate instantiation of the inferred type scheme, an untyped term can safely be used as a value of various different types.
  This approach not only captures the polymorphic nature of functions on records but also integrates record polymorphism and ML-style type inference, which relieves the programmer from writing complicated type declarations required in explicit second-order calculi.

  Most of the proposed type inference systems have been based on the mechanism of row variables [Wand 1987], which are variables ranging over finite sets of field types.

  Fig. 1. Example of programs with their inferred types.

  Here, instead of using row variables, we base our development on the idea presented in Ohori and Buneman [1988] of placing restrictions on possible instantiations of type variables.
  We formalize this idea as a kind system of types and refine the ordinary type quantification to kinded quantification of the form `∀t::k.σ` where type variable `t` is constrained to range only over the set of types denoted by a kind `k`.
  This mechanism is analogous to bounded quantification [Cardelli and Wegner 1985].
  A kind `k` is either the universal kind `U` denoting the set of all types, a record kind of the form `{{l1:τ1,···,tn:τn}}` denoting the set of all record types that contain the specified fields, or a variant kind of the form `<<l1:τ1,···,tn:τn>>` denoting the set of all variant types that contain the specified fields.

  This mechanism allows us to represent polymorphic types of various record operations.
  For example, the function name and the value payment are given the following types:

    name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1
    payment : ∀t::<<Pound : real>>.t

  indicating that `name` is a function that takes a value of any record type containing a `Name:t1` field and returns a value of type `t1` where `t1` may be any type, and payment is a polymorphic value having any variant type containing a `Pound:real` component.
  By this mechanism, these terms can be used polymorphically.
  In addition to labeled-field access, kinded abstraction can also be used to represent polymorphic record modification (update) operations `modify(e1,l,e2)`, which creates a new record from `e1` by modifying the value of the `l` field to `e2`, leaving all the other fields unchanged.
  The following typing shows the polymorphic nature of this construct.

    λx.λy.modify(y,l,x) : ∀t1::U.∀t2::{{l:t1}}.t1→t2→t2

  Combination of these features allows flexible programming without sacrificing the advantage of static typing and the existence of an ML-style, complete, type inference algorithm.
  Figure 1 shows examples of typings involving labeled records and variants using ML-style polymorphic function declaration.

  This form of programming is also possible in the other proposals for ML-style polymorphic record calculi based on row variables mentioned earlier.
  One advantage of our formulation is that it yields a uniform treatment for both explicitly typed calculi and ML-style type inference systems.
  Most of the type inference algorithms are defined without second-order types and do not explicitly treat ML’s let binding.
  Rémy [1994b] formally treats ML’s let binding.
  However, its relationships to an explicitly typed second-order system have not been well investigated.
  Using kinded abstraction, we extend the second-order lambda calculus of Girard [1971] and Reynolds [1974] to record polymorphism and show that the extension preserves basic properties of the second-order lambda calculus.
  We then develop an ML-style type inference system for a predicative subset of the second-order lambda calculus.
  These results extend the type inference algorithm of Milner [1978], the type system for ML let polymorphism by Damas and Milner [1982], and the analysis on the relationship between ML polymorphism and a predicative second-order system by Harper and Mitchell [1993].
  These connections will allow us to transfer various known results of polymorphic type discipline to record polymorphism.

  It should be mentioned, however, that row variables appear to be better suited to represent various powerful operations on records.
  Among the type systems based on row variables, perhaps the most flexible is that of Rémy [1994b], which uses sorted equational theory on row variables.
  For polymorphic record field access, record modification and polymorphic variants, his type system provides polymorphic typings equivalent to ours.
  For example, the function name is given the following typing in his system:

    λx.x#Name : (ρ {Name} ; Name : pre(t)) → t

  where ρ {Name} is a sorted row variable representing possible rows (finite sets of record fields) that do not contain a `Name` field, and `pre(t)` indicates the existence of `Name` field of type `t`.
  This typing is equivalent to the typing in our calculus in the sense that the two denote the same set of ground instances.
  However, his system is more powerful in that it can also represent an operation that extends a record with a new field and one that removes an existing field from a record, which are not representable in our type system.
  A restricted form of record extension operation is supported in Jategaonkar and Mitchell [1993].
  Explicitly typed second-order calculi for extensible records have also been proposed [Cardelli and Mitchell 1989; Harper and Pierce 1991].
  Unavailability of these extension operations is a limitation of our type system.
  However, those record calculi based on row variables appear to be difficult to compile.
  To the author’s knowledge, there is no known systematic compilation method for any of these record calculi.
  A significant advantage of our type system is that it allows us to develop an efficient compilation method that always compile out labeled-field access into a direct index operation, as we shall explain in the next subsection.

# 1.2 Compilation Method for Record Polymorphism

  The second technical challenge in developing a practical programming language with record polymorphism is compilation.
  An important property of labeled records is the ability to access an element in a record not by position but by label, i.e., symbolic name.
  In a statically typed monomorphic language, this does not cause any difficulty in compilation.
  Since the actual position of each labeled field is statically determined from the type of a record, labeled-field access is easily compiled into an index operation, which is usually implemented by a single machine instruction.
  In a language with record polymorphism, however, compilation is a difficult problem.
  Consider the function `λx.x#Name` again.
  Since actual arguments differ in the position of the Name field, it appears to be impossible to compile this function into a function that performs an index operation.

  One straightforward approach might be to predetermine the offsets of all possible labels and to represent a record as a potentially very large structure with many empty slots.
  Cardelli [1994] took this strategy to represent records in a pure calculus of subtyping.
  Although this approach would be useful for studying formal properties of record polymorphism, it is unrealistic in practice.
  Another naive approach is to directly implement the intended semantics of the labeled-field access by dynamically searching for the specified label in a record represented as an association list of labels and values.
  An obvious drawback to such an approach is inefficiency in runtime execution.
  Since field access is the basic operation that is frequently invoked, such a method is unacceptable for serious application development.

  A more-realistic approach for dynamic field lookup is to use a form of hashing.
  Rémy [1994a] presented an efficient, dynamic, field lookup method using a form of hashing similar to extendible hashing [Fagin et al. 1979] and showed that field selection can be implemented with relatively small runtime overhead both in execution time and in extra memory usage.
  This can be a reasonable implementation technique for various record calculi where static determination of the position of labeled fields is impossible.
  A drawback of this method is that labeled-field access always incurs extra runtime overhead, even when the program is completely monomorphic, and therefore the positions of labels can be statically determined.
  It would be unfortunate if we were forced to pay extra penalty for monomorphic labeled-field access when we move to a supposedly more advanced language with a polymorphic type system.
  Another drawback of hashing is that there is no guarantees to work for arbitrary records.
  Remy’s technique, for example, does not work well for large records such as those with 50 or 100 fields.

  <!--7-->

  For a polymorphic record calculus to become a basis of practical programming languages, we must develop a compilation method that always achieves both compactness in the representation of records and efficiency in the execution of labeled-field access.
  Connor et al. [1989] considered this problem in the context of an explicitly typed language with subtyping and suggested an implementation strategy.
  However, they did not provide a systematic method to deal with arbitrary expressions, nor did they consider a type inference system.
  The second goal of this article is to develop such a compilation method and to establish that compilation achieves the intended operational behavior of a polymorphic record calculus.

  Our strategy is to translate a polymorphic record calculus into an implementation calculus.
  In the implementation calculus, a labeled record is represented as a vector of values ordered by a canonical ordering of the set of labels, and fields are accessed by direct indexing.
  A variant value is represented as a value tagged with a natural number indicating the position in the vector of functions in a switch statement.
  To deal with polymorphic field selection and polymorphic variants, the implementation calculus contains index variables and index abstraction.
  For example, from an untyped term

    let name = λx.x#Name in (name {Name=”Joe”, Office=403},
                             name {Name=”Hanako”, Age=21, Phone=7222})

  the translation algorithm produces the following implementation code:

    let name = λIλx.x[I] in ((name 1) {”Joe”,403}, (name 2) {21,”Hanako”,7222})

  where I is an index variable;
  λI. M is index abstraction;
  x[I] is an index expression;
  {”Joe”,403} and {21,”Hanako”,7222} are vector representations of the records whose fields are ordered by the lexicographical ordering on labels;
  and (name 1) and (name 2) are index application supplying appropriate index values to the index variable I.
  Similarly, an untyped term

    let payment = <Pound=100.0>
    in (case payment of <Pound=λx.x, Dollar=λx.x * 0.68>,
        case payment of <Pound=λx.real to int(x * 150.0), Yen = λx.x>)

  is translated into the following code in the implementation calculus:

    let payment = λI.<I=100.0>
    in (switch (payment 2) of <λx.x * 0.68, λx.x>,
        switch (payment 1) of <λx.real to int(x * 150.0), λx.x>)

  where a polymorphic variant payment is represented as a term containing index abstraction whose index value is supplied through index applications — (payment 1), (payment 2) — and is used to select the corresponding function in the function vector in a switch statement whose elements are sorted by the lexicographical ordering on the variant labels.

  Our compilation method works for arbitrary records and variants and does not introduce any runtime overhead for monomorphic programs.
  For polymorphic record functions and variants, it requires extra function applications to pass index values before applying them.
  However, as we shall show in the following development, extra index applications are done only when polymorphic terms are instantiated.
  So we believe that their cost is negligible.

  <!--8-->

  The general idea of passing index values was suggested in Connor et al. [1989].
  One of our original contributions is (1) to establish a systematic compilation algorithm that always constructs a correct implementation term for any type correct raw term of a polymorphic record calculus and (2) to establish its correctness formally.

# 3.3 Explicitly Typed Calculus Λlet,# Corresponding to λlet,#

    M ::= (x τ···τ) | cb | λx:τ.M | M M | Poly(M:σ) | let x:σ = M in M
        | {l=M,···,l=M} | M:τ#l | modify(M:τ,l,M)
        | (<l=M>:τ) | case M of <l=M,···,l=M>

  Syntax

<!--27 868-->

# 4. COMPILATION

  This section develops an algorithm to compile the ML-style polymorphic record calculus `λlet,#` into an implementation calculus `λlet,[]`, defined below.

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

  Fig. 12. Call-by-value evaluation operational semantics of λlet,[].

## 4.1 Implementation Calculus : λlet,[]

  We define an implementation calculus with directly indexable vectors and `switch` statements on integer tags as an efficient abstract machine for polymorphic record calculi.

  As we shall see later, index values are always computed statically by our compilation algorithm defined later, and there is no need to treat them as first-class values.
  So we introduce the following new syntactic category of indexes (ranged over by `Ï`) and treat them specially:

    Ï ::= I | i
    where
      I stands for a given set of index variables and
      i for natural numbers.

  The set of raw terms of λlet,[] (ranged over by `C`) is given by the syntax:

    C ::= x | c b |λx.C | C C | let x=C in C | {C,···,C} | C[Ï]
        | modify(C,Ï,C) | <Ï=C> | switch C of C,···,C | λI.C | C Ï
    where
      {C1,···,Cn} is a vector representation of a record;
      C[Ï] is index expression retrieving the element of index value Ï from vector C;
      switch C of C1,···,Cn analyzes the integer tag of a variant C and
                            applies the corresponding function Ci to the value of C;
      λI.C is index abstraction; and
      C Ï is index application.

  As in `λlet,#`, call-by-value operational semantics is defined using evaluation contexts (ranged over by `EV[]`), the set of values (ranged over by `V`), and call-by-value context-rewriting axioms of the form `EV[C1] −→ EV[C2]`.
  We say that `C` evaluates to `C'` in one step, written `C −EV→ C'`, if there are `EV[]1`, `C1`, `C2` such that `C = EV[C1]1`, `EV[C1]1 −EV→ EV[C2]1`, and `C' = EV[C2]1`.
  We write `−EV→→` for the reflexive transitive closure of `−EV→`; we write `C↓C'` if `C −EV→→ C'` and if there is no `C''` such that `C' −EV→ C''`; and we write `C↓` if `C↓C'` for some `C'`.
  Figure 12 gives a mutual recursive definitions of the set of values,call-by-value evaluation contexts, and the set of context-rewriting axioms of λlet,[].

<!--27 870-->

## 4.2 The Type System of λlet,[]

  To establish the correctness of the compilation algorithm defined in the following subsection, we define a type system for the implementation calculus.

  To represent labeled records and labeled variants in the implementation calculus, we assume a total order `<<` on the set of labels and restrict that a record type `{l1:τ1,···,ln:τn}` or a variant type `<l1:τ1,···,ln:τn>` must satisfy the condition `l1<<···<<ln`.
  The usual choice for `<<` is the lexicographical ordering on the string representations of labels.
  If `τ` is one of the above forms, we define the index of a label `li` in `τ` to be `i`.
  A record term of the above record type is a vector whose `i`th element is `li` field.
  An `li` variant of the above variant type is a value tagged with integer `i` manipulated by a `switch` statement containing a vector of functions whose `j`th element corresponds to the function for `lj` variant.
  For example, if a record type consists of an Age field of type `int` and a Name field of type `string`, then it must be of the form `{Age:int,Name:string}`, and thus the index of `Name` in this record type is `2`.
  A possible term of this type includes `{21,"Joe"}`, which corresponds to `{Name="Joe",Age=21}` in λlet,#.
  Similarly, a variant type with `Pound` variant of type real and `Dollar` variant of type real must be of the form `<Dollar:real,Pound:real>`, and thus the index of `Pound` in the type is `2`.
  A `switch` statement for this type consists of a vector of functions for `Dollar` and `Pound` in this order, and a `Pound` variant of `100.0` of this type is represented as `<2=100.0>`, which corresponds to a (monomorphic) term of `<Pound=100.0>` of the above type in λlet,#.

  To account for polymorphic operations,we introduce a new form of types `idx(l,τ)` for index values.
  When `τ` is a record type or a variant type,this type denotes the index of `l` in `τ`.
  We write `|idx(l,τ)|` for the index value denoted by `idx(l,τ)`.
  For example, `|idx(Name,{Age:int,Name:string})| = 2`.
  When `τ` is a type variable `t`, then `idx(l,t)` denotes possible index values depending on instantiations of `t`, and `|idx(l,t)|` is undefined.

  The set of types of the implementation calculus is given by the following syntax:

    τ ::= t | cb | τ→τ | {l:τ,···,l:τ} | <l:τ,···,l:τ> | idx(l,τ) ⇒ τ
    σ ::= τ | ∀t::k.σ

  where `idx(l,τ1)⇒τ2` denotes functions that take an index value denoted by `idx(l,τ1)` and yield a value of type `τ2`.
  Since index values are not first-class objects, it is not necessary to included index types `idx(l,τ)` as separate types.
  The set of kinds and the kinding rules are the same as those of λlet,#.

  The type system of this calculus is defined as a proof system for the following forms of judgments:

    K,L,T ▷ C : τ       typing judgment
    L |- I : idx(l,τ)    index judgment

  where `K` is a kind assignment and `T` a type assignment as in the previous calculi.
  `L` is an index assignment, which is a mapping from a set of index variables to index types of the form `idx(l,τ)`.
  A type `τ` is well formed under `K` if `FTV(τ) ⊆ dom(K)` and if for any type of the form `idx(l,τ')` appearing in `τ,τ'` has a record kind or variant kind containing `l` field under `K`.
  A type `∀t1::k1···tn::kn.τ` is well formed under `K` if `τ` is well formed under `K{t1::k1···tn::kn}`.
  `L` is well formed under `K` if each type in `L` is well formed under `K`.
  A type assignment `T` is well formed under `K` if each type in `T` is well formed under `K`.

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

  Fig. 13. Typing rules for the implementation calculus λlet,[].

  The set of typing rules is given in Figure 13.
  Since we are not concerned with type inference of λlet,[], we adopt a more-general and more-natural rule for GEN than the one we used for λlet,#.
  This makes the proof of the subject reduction property below slightly easier.
  We write `λlet,[] |- K,L,T ▷ C : σ` if `K,L,T ▷ C : σ` is derived in this poof system.
  It is easily verified that if `λlet,[] |- K,L,T ▷ C : σ` then `σ` is well formed under `K`.

<!--29 872-->

    (β)       (λx.C1) C2                ⟹ [C2/x]C1
    (index)   {C1,···,Cn}[i]            ⟹ Ci (1 ≤ i ≤ n)
    (modify)  modify({C1,···,Cn},i,C)   ⟹ {C1,···,Ci−1,C,Ci+1,···,Cn} (1 ≤ i ≤ n)
    (switch)  switch <i=C> of C1,···,Cn ⟹ Ci C (1 ≤ i ≤ n)
    (iapp)    (λI.C) Ï                  ⟹ [Ï/I]C
    (let)     let x=C1 in C2            ⟹ [C1/x]C2

  Fig. 14. The reduction rules for the implementation calculus λlet,[].

  For this type system, we show the subject reduction property, which will be useful later in establishing that our compilation algorithm preserves the operational behavior of λlet,#.
  Since our usage of λlet,[] is as an abstract machine to implement λlet,#, we do not need a stronger property of type soundness of λlet,[] itself.
  The type soundness of λlet,# with respect to the operational semantics of the compiled term of λlet,[] will follow from the correctness of compilation we shall establish later.

  The reduction axioms for λlet,[] are given in Figure 14.
  We say that `C1` reduces to `C2` in one step, written `C1→C2`, if `C2` is obtained from `C1` by applying one of the reduction axioms to some subterm of `C1`.
  The reduction relation `C1→→C2` is defined as the reflexive transitive closure of `→`.
  The following substitution lemmas are useful in proving the subject reduction theorem.

#### Lemma 4.2.1.

  If `λlet,[] |- K,L,T {x : σ1} ▷ C1 : σ2` and `λlet,[] |- K,L,T ▷ C2 : σ1` then `λlet,[] |- K,L,T ▷ [C2/x]C1 : σ2`.

#### Proof.

  The proof is by induction on the typing derivation of `C1`.
  The only interesting case is variable axiom.
  Other cases are similar to Lemma 2.2.4.

  Suppose `K,L,T{x:σ1} ▷ y : τ2` is a VAR axiom.
  The case for `x /= y` is trivial.
  Suppose `x = y`. Let `σ1 = ∀t1::k1···tn::kn.τ1`. Then `K |- ∀t1::k1···tn::kn.τ1 ≥ τ2` and therefore there must be some `S` such that `dom(S) = {t1,···,tn},(K,S)` respects `K{t1::k1···tn::kn}` and `S(τ1) = τ2`.
  If `n = 0`, i.e., `σ1` is a monotype, then `σ1 = τ2`, and therefore `λlet,[] |- K,L,T ▷ C2 : τ2`.
  Otherwise `K,L,T ▷ C2 : σ1` must be derived by GEN, and therefore `λlet,[] |- K{t1::k1···tn::kn},L,T ▷ C2 : τ1` such that `{t1,···,tn}` does not appear in `T` or `L`.
  By Lemma 2.2.3 for λlet,#, we have `λlet,[] |- K,L,T ▷ C2 : τ2`. □

#### Lemma 4.2.2.

  If `λlet,[] |- K,L{Ï:idx(l,τ1)},T ▷ C : τ` and `L |- Ï : idx(l,τ1)` then `λlet,[] |- K,L,T ▷ [Ï/I]C : τ`.

#### Proof.

  This is provde by induction on the typing derivation of `C`.
  We only show the case for rule INDEX.
  The cases for IAPP, MODIFY, and VARIANT can be shown similarly.
  All the other cases follow directly from the induction hypothesis.

  Suppose `K,L{Ï:idx(l,τ1)},T ▷ C1[Ï1] : τ` is derived by rule INDEX from `K,L{Ï:idx(l,τ1)},T ▷ C1 : τ2`, from `K |- τ2::{{l':τ}}`, and from `L{Ï:idx(l,τ1)} |- Ï1 : idx(l',τ2)`.
  By the induction hypothesis, `λlet,[] |- K,L,T ▷ [Ï/I]C1 : τ2`.
  There are two cases to be considered.
  First, suppose `Ï1=I`.
  Then we have `τ1 = τ2` and `l = l'`, and therefore `K |- τ2::{{l:τ}}` and `L |- Ï : idx(l,τ2)`.
  By the typing rule, `λlet,[] |- K,T ▷ ([Ï/I]C1)[Ï] : τ`, i.e., `λlet,[] |- K,T ▷ [Ï/I](C1[I]) : τ`.
  Second, suppose `Ï1 /= I`. todo
  Then either `|idx(l',τ2)|` is defined and `Ï1 = |idx(l',τ2)|` or `Ï1 ∈ dom(L)`.
  In either case, `L |- Ï1 : idx(l',τ2)` and by the typing rule, `λlet,[] |- K,T ▷ ([Ï/I]C1)[Ï1] : τ`.
  But `[Ï/I](C1[Ï1]) = ([Ï/I]C1)[Ï1]`. □

<!--30 873-->

#### Theorem 4.2.3. If `λlet,[] |- K,T,L ▷ C1 : σ` and `C1 →→ C2` then `λlet,[] |- K,T,L ▷ C2 : σ`.

#### Proof.

  It is sufficient to show the theorem for monotypes.
  The proof is similar to Theorem 2.2.5 using the above two substitution lemmas. □

## 4.3 Compilation Algorithm

  We develop a compilation algorithm for λlet,# using type information obtained by type inference.
  The type inference algorithm has already converted a given λlet,# term into an explicitly typed term of Λlet,#, which contains all the type information necessary for compilation.
  So we present the compilation algorithm as an algorithm to compile Λlet,# terms into λlet,[] terms.

  As explained in the introduction, our strategy for compiling polymorphic functions containing polymorphic record operations is to insert appropriate index abstractions.
  Under this strategy, a polymorphic function of type `σ` in λlet,# is compiled into a term having the type that is obtained from `σ` by inserting necessary index abstractions indicated by the kinded type quantifiers of `σ`.
  To establish the relationship formally between the type of a source code and the type of the compiled code, we first define the following auxiliary notions.

  The set of index types contained in `t` of kind `k`, denoted by `IdxSet(t::k)`, is defined as the following set.

    IdxSet(t::U) = ∅
    IdxSet(t::{{F}}) = {idx(l,t)|l ∈ dom(F)}
    IdxSet(t::<<F>>) = {idx(l,t)|l ∈ dom(F)}

  This definition is extended to polytypes and kind assignments as follows:

    IdxSet(∀t1::k1···tn::kn.τ) = IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)
    IdxSet(K) = ∪{IdxSet(t::k)|(t::k) ∈ K}

  For a given type σ of λlet,#, the corresponding type `(σ)*` of λlet,[] is defined as

    (∀t1::k1···tn::kn.τ)* = ∀t1::k1···tn::kn.idx(l1,t1')⇒···idx(lm,tm')⇒τ

  such that `idx(l1,t1'),···,idx(lm,tm')` is the set of index types in `IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)` ordered as: `idx(l,ti)` precedes `idx(l',tj)` iff `i < j` or `i = j` and `l << l'`.
  In particular, `(τ)* = τ` for any monotype `τ`.
  The following is an example.

    (∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.t2→t3)* =
      ∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.idx(a,t2)⇒idx(b,t2)⇒idx(a,t3)⇒t2→t3

  This definition is extended to type assignments as follows:

    (T)* = {x : (T(x))* |x ∈ dom(T)}

  For a kind assignment `K`, define the index assignment `LK` determined by `K` as `LK = {I : idx(l,t)|idx(l,t) ∈ IdxSet(K),each I fresh}`.

<!--31 874-->

  The compilation algorithm is given in Figure 15 as an algorithm `C` that takes `LK,(T)*` and `M` and computes a term of the implementation calculus.
  Since `LK` has the property that there is at most one `(I,idx(l,t)) ∈ LK` for any pair `(l,t)`, each `Ï` mentioned in the algorithm is unique, and therefore `C` is a deterministic algorithm.

  The compilation preserves types as shown in the following theorem.

#### Theorem 4.3.1.

  If `Λlet,# |- K,T ▷ M : σ`, then `C(LK,(T)*,M)` succeeds with `C` such that `λlet,[] |- K,LK,(T)* ▷ C : (σ)*`.

#### Proof.

  This is provded by induction on the structure of `M`.
  Here we show the cases for variables, field selection, and generalization.
  Cases for variants and modify expressions can be shown similar to that of field selection.
  All the other cases follow easilily from the corresponding induction hypotheses.

  `(x τ1···τn)`: Suppose `Λlet,# |- K,T ▷ (x τ1···τn) : τ`. Let `S = [τ1/t1,···,τn/tn]`.
  Then `T(x) = ∀t1::k1···∀tn::kn.τ0,K |- S(ti) :: S(ki)` and `τ = S(τ0)`.
  By the definition of `(T)*`, `(T)* (x) = ∀t1::k1···∀tn::kn.idx(l1,t1')⇒···idx(lm,tm')⇒τ0` such that `{idx(l1,t1'),···,idx(lm,tm')} = IdxSet(∀t1::k1···∀tn::kn.τ0)`.
  By the rule VAR, `λlet,[] |- K,LK,(T)* ▷ x : idx(l1,S(t1'))⇒···idx(lm,S(tm'))⇒S(τ0)`.
  Let `Ïi` be those mentioned in the algorithm.
  For each `idx(l,S(ti'))`, if `S(ti')` is a type variable `t` then `t ∈ dom(K)`, and therefore by the property of `LK`, there is `Ii` such that `(Ii:idx(l,S(ti'))) ∈ LK`, and `Ïi = Ii`.
  If `S(ti')` is not a type variable then `Ïi = |idx(li,S(ti'))|`.
  Therefore in either case `LK |- Ïi : idx(l,S(ti'))`.
  Therefore the algorithm succeeds with `(x Ï1···Ïm)` and `λlet,[] |- K,LK,(T)* ▷ (x Ï1···Ïm) : τ`.

  `M1 : τ1#l`: Suppose `Λlet,# |- K,T ▷ M1 : τ1#l : τ2`.
  Then `Λlet,# |- K,T ▷ M1 : τ1` and `K |- τ1 :: {{l:τ2}}`.
  By the induction hypothesis, `C(LK,(T)*,M1) = C1` such that `λlet,[] |- K,LK,(T)* ▷ C1 : τ1`.
  Let `Ï` be the one mentioned in the algorithm.
  If `τ1` is a type variable `t`, then `t ∈ dom(K)`.
  Since `K |- t :: {{l:τ2}}`, `K(t) = {{F}}` such that `F` contains `l : τ2`.
  Then by the property of `LK`, there is some `I` such that `(I:idx(l,t)) ∈ LK` and `Ï = I`.
  If `τ1` is not a type variable then `|idx(l,τ1)| = i` for some integer `i` and `Ï = i`.
  Therefore in either case `LK |- Ï : idx(l,τ1)`.
  Then `C(LK,(T)*,M1:τ1#l)` succeeds with `C1[Ï]` and `λlet,[] |- K,L K,(T)* ▷ C1[Ï] : τ2`.

  `Poly(M:σ)`: Suppose `Λlet,# |- K,T ▷ Poly(M:σ) : σ`.
  Then `σ = ∀t1::k1···∀tn::kn.τ` such that `Λlet,# |- K',T ▷ M : τ`, `Cls(K',T,τ) = (K,∀t1::k1···∀tn::kn.τ)`.
  Let `∀t1::k1···∀tn::kn.idx(l1,t1')⇒···⇒idx(lm,tm')⇒τ1 = (σ)*`.
  Then `LK' = LK{I1:idx(l1,t1'),···,Im:idx(lm,tm')} (I1,···,Im fresh)`.
  By the induction hypothesis, `C(LK',(T)*,M) = C` such that `λlet,[] |- K',LK',(T)* ▷ C : τ`.
  Then `C(LK,(T)*,Poly(M:σ))` succeeds with `λI1···λIm.C`.
  By applying the rule IABS to `λlet,[] |- K',LK',(T)* ▷ C : τ` repeatedly, we have `λlet,[] |- K',LK,T ▷ λI1···λIm.C : idx(l1,t1')⇒···idx(lm,tm')⇒τ`.

  Since `LK` is well formed under `K,ti /∈ FTV(LK ∪ (T)*) (1 ≤ i ≤ n)`.
  Therefore we have `λlet,[] |- K,LK,(T)* ▷ C : (∀t1::k1···∀tn::kn.τ)*`, as desired. □

  Combining this result with Theorem 3.5.1, we have the following.

#### Corollary 4.3.2. If `WK(K,T,e) = (K',S,M,σ)` then `λlet,# |- K',S(T) ▷ e : σ` and `C(LK',(S(T))*,M)` succeeds with `C` such that `λlet,[] |- K',LK',(S(T))* ▷ C : (σ)*`.

<!--32 875-->

    IdxSet(t::U) = ∅
    IdxSet(t::{{F}}) = {idx(l,t)|l ∈ dom(F)}
    IdxSet(t::<<F>>) = {idx(l,t)|l ∈ dom(F)}

    IdxSet(∀t1::k1···tn::kn.τ) = IdxSet(t1::k1) ∪···∪ IdxSet(tn::kn)
    IdxSet(K) = ∪{IdxSet(t::k)|(t::k) ∈ K}


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

  Fig. 15. Compilation algorithm.

<!--33 876-->

  The above result shows that the compilation algorithm maps a term of type `σ` to a term of type `(σ)*`.
  Since `(τ)* = τ`, the compilation preserves all the monotypes.

## 4.4 Eliminating Vacuous Type Variables from λlet,# Typing

  The above algorithm translates a kinded typing of Λlet,# into a kinded typing of λlet,[].
  For this to serve as a compilation algorithm for λlet,#, there is one subtle point to be taken care of.
  This is related to the problem of coherence [Breazu-Tannen et al. 1991].
  As shown in Ohori [1989], Damas-Milner system of ML is not coherent with respect to Core XML, and the same is true for the relationship between λlet,# and Λlet,#.
  (See also Harper and Mitchell [1993] for a related discussion.)

  The source of the failure of coherence is free type variables used in a typing derivation that do not appear in the type or the type assignment in the result typing.
  Those type variables also cause a problem in applying the compilation algorithm developed in the previous subsection.
  To see this, consider the raw term `(λx.cb) (λx.(x#l) + 1)`.
  The type inference algorithm produces the following typing in λlet,#,

    {t::{{l : int}}},∅ ▷ (λx.cb) (λx.(x#l) + 1) : b

  corresponding to the following typing in Λlet,# :

    {t::{{l : int}}},∅ ▷ (λx:t → int.cb) (λx:t.(x#l) + 1) : b

  The kinded type variable `t` is introduced to typecheck polymorphic field selection `x#l`, but it does not appear in the type assignment or the result type and therefore will never be further instantiated.
  As a consequence, the given closed term is translated to an open term in Λlet,# containing a free index variable denoting the position of `l` which will not be determined.

  Our solution to this problem is to refine the Milner-style type inference algorithm given in Section 3 to eliminate these "redundant" or vacuous type variables.
  We say that a type variable `t` in `K,T ▷ e : τ` is vacuous if `t ∈ dom(K)` and `t ∈/ EFTV(K,τ) ∪ EFTV(K,T)`.

  We assume that there is a predefined base type `b0`.
  The choice of `b0` is unimportant.
  Let `K,T ▷ e : τ` be a typing, and let `t` be a vacuous type variable of the typing such that `t ∈/ FTV(K(t))`.
  Then `K` is written as `K'{t::k}`.
  Define the canonical instance `τt` of `t` in `K` as follows:

          b0    if k = U
    τt =  {F}   if k = {{F}}
          <F>   if k = <<F>>

  We can eliminate `t` from the typing by applying kinded substitution `(K',[τt/t])`.
  If the set of vacuous type variables has no mutual cyclic dependency in `K`, then it has a sequence `t1,···,tn` such that `ti ∈/ FTV(K(tj))` if `1 ≤ i ≤ j ≤ n`.
  Then by repeating the above process for `t1,···,tn`, we obtain a sequence of kinded substitution `(Ki,[τti/ti])`.
  We define a canonical instantiation for `K,T ▷ e : τ` as a kinded substitution `(Kn,[τn/tn] ◦···◦ [τi/t1])`.
  From this definition, the following results can be easily proved.

#### Lemma 4.4.1.

  If `(K0,S0)` is a canonical instantiation of a typing `K,T ▷ e : τ`, then `(K0,S0)` respects `K`.

<!--34 877-->

  By Lemma 2.2.3, we have the following.

#### Corollary 4.4.2.

  If `λlet,# |- K,T ▷ e : τ` and `(K0,S0)` is a canonical instantiation of `K,T ▷ e : τ` then `λlet,# |- K0,T ▷ e : τ`.

  This shows that if the set of vacuous type variables has no cyclic dependency then we can eliminate them without affecting the typing property of the term.
  We call `K0,T ▷ e : τ` the canonical instance of `λlet,# |- K,T ▷ e : τ`.

  We identify a program in λlet,# as a closed typing of the form:

    ∅,∅ ▷ e : σ

  We refine the type inference algorithm defined in the previous section so that just before the type abstraction at the top level it takes a canonical instance of the inferred typing if one exists; otherwise it reports type error.
  Since a program must have a closed typing, and therefore its derivation does not contain a kind assignment with cyclic dependency, this process does not change the typability of programs.
  From a program of the above form of λlet,# the refined type inference algorithm produces the following closed typing of Λlet,#

    ∅,∅,∅ ▷ Poly(M:σ) : σ

  We regard these closed typings as units of separate compilation.

  With this refinement,the compilation algorithm given in the previous subsection serves as a compilation algorithm for λlet,#.
  Corollary 4.3.2 becomes the following.

#### Corollary 4.4.3.

  If `e` is a well typed λlet,# program, then `WK(∅,∅,e)` succeeds with `(∅,S,M,σ)` for some `S,M,σ` such that `λlet,# |- ∅,∅ ▷ e : σ`,`Λlet,# |- ∅,∅ ▷ M : σ`, and `C(∅,∅,M)` succeeds with `C` such that `λlet,[] |- ∅,∅,∅ ▷ C : (σ)∗`.

  Let us show examples of compilation.
  From a λlet,# term `λx.x#Name`, the type inference process produces the following program

    Λlet,# |- ∅,∅ ▷ Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)
                  : ∀t1::U.∀t2::{{Name:t1}}.t2→t1

  For this program, the compilation algorithm produces the following result

  C(∅,∅,Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)) = λI.λx.x[I]

  which has the following typing:

    λlet,[] |- ∅,∅,∅ ▷ λI.λx.x[I] : ∀t1::U.∀t2::{{Name:t1}}.idx(Name,t2) ⇒ t2→t1

  A program

    let name=λx.x# Name in (name {Name="Joe",Office=403},
                            name {Name="Hanako",Age=21,Phone=7222})

  is converted to the following program in Λlet,# as seen in the previous section:

    E ≡ let name:∀t1::U.∀t2::{{Name:t1}}.t2→t1
              = Poly(λx:t2.x#Name : ∀t1::U.∀t2::{{Name:t1}}.t2→t1)
        in ((name string {Name:string,Office:string})
              {Name="Joe",Office=403},
              (name string {Name:string,Age:int,Phone:int})
              {Name="Hanako",Age=21,Phone=7222})

<!--35 878-->

  and the compilation algorithm produces the following result

    C(∅,∅,E) = let name=λI.λx.x[I] in (name 1 {"Joe",403},
                                        name 2 {21,"Hanako",7222})

  which has the expected typing and evaluates to `("Joe","Hanako")`.

  The next is an example of a program involving polymorphic variant and vacuous type variable elimination.
  The following program of λlet,#

    let point = <Cartesian={X=2.0,Y=3.0}> in
      case point of <Cartesian=λc.sqroot(square(c#X) + square(c#Y)),Polar=λp#R>

  is converted into the following program in Λlet,#.

    F ≡ let point:∀t::<<Cartesian:{X:real,Y:real}>>.t
            = Poly((<Cartesian={X=2.0,Y=3.0}>:t)
                    : ∀t::<<Cartesian:{X:real,Y:real}>>.t)
        in case (point <Cartesian:{X:real,Y:real},Polar:{R:b0}>) of
           <Cartesian=λc:{X:real,Y:real}.sqroot(square(c#X)+square(c#Y)),
            Polar=λp:{R:b0}.x#R>

  From this, the compilation algorithm produces the following code:

    C(∅,∅,F) = let point=λI.<I={2.0,3.0}>
                 in switch (point 1) of <λc.sqroot(square(c[1]) + square(c[2])),λx.x[1]>

  Note that vacuous type variable elimination is properly performed for `Polar` branch of the `case` statement, and the unused field extension `x#R` is compiled into index expression with the default index value `1`.

## 4.5 Correctness of Compilation

  In Section 4, we have shown that the compilation algorithm preserves typing.
  This section shows that the compilation algorithm also preserves the operational behavior of a program.
  Since we have shown that the type system of λlet,# is sound with respect to its operational semantics,the preservation of operational behavior will also establish that the type system of λlet,# is sound with respect to the operational semantics of the compiled code in λlet,[].

  For terms of base types, the desired property is simply being that the original term and the compiled term evaluate to the same constant value.
  We need to generalize this to arbitrary types including polytypes.
  Our strategy is to apply the idea of logical relations to lift the above relationship to arbitrary types.

  Let `σ` be a closed type of λlet,#.
Let term `σ` be the set `{e|λlet,# |- ∅,∅ ▷ e : σ}`, and let `Termσ` be the set `{M|λlet,[] |- ∅,∅,∅ ▷ M : (σ)*}`.
We define a type-indexed family of relations `{Rσ ⊆ termσ × Termσ}` by induction on `σ` as follows.

    (e,C) ∈ R σ ⇐⇒ (1) e ↓ iff C ↓ and
                      (2) one of the following conditions holds

  — if `σ = b` then if `e ↓ e'` and `C ↓ C'` then `e' = C'`.

  — if `σ = τ1→τ2` then for any `e0`, `C0` such that `(e0,C0) ∈ Rτ1`, `(e e0,C C0) ∈ Rτ2`.

  — if `σ = {l1:τ1,···,ln:τn}` then if `e ↓ e'` and `C ↓ C'` then `e' = {l1=e1,···,ln=en}`, `C' = {C1,···,Cn}` such that `(ei,Ci) ∈ Rτi` for all `1 ≤ i ≤ n`.

<!--36 879-->

  — if `σ = <l1:τ1,···,ln:τn>` then if `e ↓ e'` and `C ↓ C'` then there is some `i` such that `e' = <li= e''>`, `C' = <i=C''>` and `(e'',C'') ∈ Rτi`.

  — if `σ = ∀t1::k1.···tn::kn.τ` such that

    (σ)* = ∀t1::k1.···tn::kn.idx(l1,t1') ⇒···idx(lm,tm')⇒τ

  then for any ground substitution `S` satisfying `{t1::k1.···tn::kn}`,

    (e,(···(C i1)···im)) ∈ R^(S(τ))

  where `ij = |S(idx(lj,tj'))| (1≤ j ≤ m)`.

  Note that by the type soundness theorem (Theorem 3.2.1) of λlet,# and the subject reduction theorem (Theorem 4.2.3) of λlet,[], if `e ∈ termσ`, `C ∈ Termσ`, `e ↓ e'`, and `C ↓ C'` then `e' ∈ termσ`, `C' ∈ Termσ`.
  Furthermore, by the definition of `Rσ`, if `(e,C) ∈ Rσ` then `(e',C') ∈ Rσ`.

  Let `T` be a closed type assignment of λlet,#.
  A `T`-environment in λlet,# is a function `η1` such that `dom(η1) = dom(T)` and for any `x ∈ dom(η1)`, `η1(x) ∈ term^(T(x))`.
  A `(T)∗`-environment in λlet,[] is a function `η2` such that `dom(η2) = dom(T)` and for any `x ∈ dom(η2), η2(x) ∈ Term^((T)∗ (x))`.
  Let `L` be a well-formed, closed, index assignment.
  A `(T)∗`-environment `η2` in λlet,[] is uniquely extended to the function defined on `dom(T)∪dom(L)` by setting its value of `I` to be `|L(I)|` for all `I ∈ dom(L)`.
  We write `ηL2` for the extension of `η2` to `dom(L)`.

  The relation `R` is extended to environments.
  `RT` is the relation between `T`-environments in λlet,# and `(T)∗`-environments in λlet,[] such that `(η1,η2) ∈ RT` iff for any `x ∈ dom(T), (η1(x),η2(x)) ∈ R^(T(x))`.

  We now have the following theorem, whose proof is deferred to the Appendix.

#### Theorem 4.5.1.

  Let `Λlet,# |- K,T ▷ M : σ` be any typing.
  If `C(LK,(T)∗,M) = C` then for any ground substitution `S` that respects `K`, and for any pair of environments `(η1,η2) ∈ R^(S(T)), (η1(erase(M)),η2_{S(LK)} (C)) ∈ R^(S(σ))`.

  For a program, we have the following.

#### Corollary 4.5.2.

  If `e` is a well-typed λlet,# program, then `WK(∅,∅,e)` succeeds with `(∅,S,M,σ)` for some `S,M,σ` and `C(∅,∅,M)` succeeds with `C` for some `C` such that `(e,C) ∈ Rσ`.

  If we define the set of observable types by the following syntax

    ω ::= b | {l:ω,···,l:ω} | <l:ω,···,l:ω>

  then the relation Rω is essentially the identity (modulo representation of records and variants), and therefore a program of an observable type in λlet,# and its compiled term evaluates to the essentially same value.

# 5. IMPLEMENTATION

  Using the polymorphic typing and the compilation method presented in this article we have extended Standard ML with polymorphic record operations,and we have implemented its compiler,called SML#.
  SML# is an extension of the Standard ML of New Jersey compiler [Appel and MacQueen 1991] on which it is based.

