:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(ics).

:- begin_tests(avs).
  test(i) :- i(1).
  test(i) :- i(10).
  test(i) :- i(-10).
  test(cb) :- cb(-10).
  test(cb) :- cb(true).
  test(cb) :- cb(false).
  test(x) :- x(x).
  test(x) :- \+x(true).
  test(x) :- \+x(1).

  test(c_xcb) :- 'C'(1),'C'(true),'C'(xxx).
  test(c_λ) :- 'C'(λ(x,x)).
  test(c_app) :- 'C'(λ(x,x)$1).
  test(c_λ) :- 'C'(λI(i,i)).
  test(c_record) :- 'C'([1,2]).
  test(c_record) :- 'C'([1,2]#[i]).
  test(c_record) :- 'C'([1,2]#[1]).
  test(c_record) :- 'C'(modify([1,2],1,2)).
  test(c_variant) :- 'C'({[1=1]}).
  test(c_variant) :- 'C'(switch(1,[λ(x,x),λ(x,add$x#[1]$x#[2])])),!.
  
:- end_tests(avs).

:- begin_tests(csub).

  test(cb) :- csub([y/x],1,1),csub([y/x],true,true),csub([y/x],false,false).
  test(x) :- csub([y/x],x,y).
  test(x) :- csub([y/x,z/y],x,z).
  test(x) :- csub([z/y,y/x],x,z).
  test(x) :- csub([y/x,z/y],x,z).
  test(x) :- csub([z/y,y/x],x,z).
  test(λ) :- csub([y/x,z/y],λ(x,x),λ(x,x)).
  test(λ) :- csub([y/x,z/y],λ(a,x),λ(a,z)).
  test(λ) :- csub([z/y,y/x],λ(a,x),λ(a,z)).
:- end_tests(csub).

:- begin_tests(eval).
  test(λ) :- λ(x,x) $ 1 ⟹* 1.
  test(record) :- ([10,20]#[1]) ⟹* 10.
  test(record) :- ([10,20]#[2]) ⟹* 20.
  test(record) :- ([(λ(x,x)$11),2]#[1]) ⟹* 11.
  test(record) :- ([(λ(x,x)$11),λ(y,y)$22]#[2]) ⟹* 22.
  test(record) :- (modify([11,22],1,10)) ⟹* [10,22].
  test(record) :- (modify([11,22],2,10)) ⟹* [11,10].
  test(record) :- (λ(z,[z])$10) ⟹* [10].
  test(record) :- (modify((λ(z,[11,z])$10),1,22)) ⟹* R,!,R=[22,10].  
  test(variant) :- ({[1=1]}) ⟹* ({[1=1]}).
  test(variant) :- (switch((λ(z,{[1=z]})$1),[λ(x,x),λ(x,add$x#[1]$x#[2])])) ⟹* 1.
  test(variant) :- (switch((λ(z,{[2=[z,10]]})$1),[λ(x,x),λ(x,[x#[2],x#[1]])])) ⟹* [10,1].
:- end_tests(eval).

:- begin_tests(τ).
  test(x) :- τ(x).
  test(b) :- τ(int).
  test(fun) :- τ(int->int).
  test(empty_record):- τ([]).
  test(one_element_record):- τ([a:int]).
  test(three_elements_record):- τ([a:int,b:int,c:bool]).
  test(nested_record):- τ([a:int,b:[a:int,c:bool]]).
  test(variant):- τ({[eint:int,eadd:['1':e,'2':e]]}).
  test(idx) :- τ(idx(a,x,int)). % todo
:- end_tests(τ).

:- begin_tests(k).
  test(k):- k(u).
  test(k):- k([]).
  test(k):- k([l::int]).
  test(k):- k({[eint::int,eadd::['1':int,'2':int],emul::['1':int,'2':int]]}),!.
:- end_tests(k).

:- begin_tests(σ).
  test(σ):- σ(∀(t,u,t)).
  test(σ):- σ(∀(t,[a::int,b::int],t)).
  test(σ):- σ(∀(t,{[a::t,b::t]},{[a:t,b:t,c:int]})),!.
  test(σ):- σ(∀(t,[a::t,b::t],[a:t,b:t,c:int])).
  test(fun) :- σ(int->int).
:- end_tests(σ).

:- begin_tests(kinding).
:- begin_var_names(['^(k|t)[0-9]*$'],['^(true|bool|int)$']).
  test(kinding_int):- [] ⊢ int::k,k=u,!.
  test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[x::int],!.
  test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[x::int,y::int],!.
  % test(kinding_t):- [a::[x::int,y::int]] ⊢ a::k,k=[y::int]. todo
  test(kinding_record):- [] ⊢ [x:int,y:int]::k,k=[x::int],!.
  test(kinding_record):- [] ⊢ [x:int,y:int]::k,k=[x::int,y::int],!.
  test(kinding_variant_t):- [a::{[x::int,y::int]}] ⊢ a::k,k={[x::int]},!.
  test(kinding_variant_t):- [a::{[x::int,y::int]}] ⊢ a::k,k={[x::int,y::int]},!.
  test(kinding_variant):- [] ⊢ {[x:int,y:int]}::k,k={[x::int]},!.
  test(kinding_variant):- [] ⊢ {[x:int,y:int]}::k,k={[x::int,y::int]},!.
:- end_var_names(_).
:- end_tests(kinding).

:- begin_tests(index_judgment).
  test('IVAR I') :- [k:idx(x,int)] ⊢ k : idx(x,int),!.
  test('IVAR i record') :- [] ⊢ 1 : idx(k,[k:int,j:int]),!.
  test('IVAR i record') :- [] ⊢ 2 : idx(j,[k:int,j:int]),!.
  test('IVAR i variant') :- [] ⊢ 1 : idx(k,{[k:int,j:int]}),!.
  test('IVAR i variant') :- [] ⊢ 2 : idx(j,{[k:int,j:int]}),!.
:- end_tests(index_judgment).

:- begin_tests(xts).
  test(abc) :- a!b!c = ((a!b)!c).
  test(xts_a) :- xts([],a, a![]).
  test(xts_ab) :- xts([],a!b, a![b]).
  test(xts_abc) :- xts([],a!b!c, a![b,c]).
  test(xts_abcd) :- xts([],a!b!c!d, a![b,c,d]).
:- end_tests(xts).

:- op(12,xf,[**]).
((A,B)**) :- B is A + 1.
:- begin_tests(*).
  test(**) :- (1,R)**,!,R=2.

  test(getT) :- getT(∀(t2,[b::int,a::bool],∀(t3,[a::t2],t2->t3)),L,T),!,
    (L/T)=[t2::[a::bool,b::int],t3::[a::t2]]/(t2->t3).
  test(*=) :- ∀(t2,[b::int,a::bool],∀(t3,[a::t2],t2->t3)) *= R,
    R= ∀(t2,[a::bool,b::int],∀(t3,[a::t2],idx(a,t2,idx(b,t2,idx(a,t3,(t2->t3)))))),!.

:- end_tests(*).

:- run_tests.
:- halt.
