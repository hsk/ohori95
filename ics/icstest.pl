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

  test(getL1):- reset,getL([],idx(b,bt,c),['%x0':idx(b,bt)],['%x0']),!.
  test(getL2):- reset,getL([],idx(a,at,idx(b,bt,c)),['%x0':idx(a,at),'%x1':idx(b,bt)],['%x0','%x1']),!.
  test(addλ) :- addλ([a,b,c,d],t,T_),T_=λ(a,λ(b,λ(c,λ(d,t)))).

:- end_tests(*).

test(_,M:_,R) :- c([],[],M,R),!.

:- begin_tests(compile).
  test(int)   :- test(10,   10   :int,10).
  test(true)  :- test(true, true :bool,true).
  test(false) :- test(false,false:bool,false).
  test(λ)     :- test(λ(x,x),
                      λ(x:'%x0',x) : ∀('%x0',u,('%x0'->'%x0')),
                      λ(x,x)).
  test(app)   :- test((λ(x,x)$1),
                      (λ(x:int,x)$1): int,
                      λ(x,x)$1).
  %test(app)  :- test(λ(t::u,λ(x:t,x)) , ∀(t,u,(t->t)).
  %test(tapp) :- test((λ(t::u,λ(x:t,x)) ! int), int->int).
  test(record) :- test([x=10,y=20],
                       [x=10,y=20]:[x:int,y:int],
                       [10,20]).
  test(record)  :- test(([x=10,y=20]#x),
                       (([x=10,y=20]:[x:int,y:int])#x):int,
                       [10,20]#[1]).
  test(record)  :- test(([x=10,y=20]#y),
                       (([x=10,y=20]:[x:int,y:int])#y):int,
                       [10,20]#[2])).
  test(record)  :- test(([x=(λ(x,x)$1),y=2]#x),
                       (([x=λ(x:int,x)$1,y=2]:[x:int,y:int])#x):int,
                       [λ(x,x)$1,2]#[1]).
  test(record)  :- test((modify([x=1,y=2],x,2)),
                        (modify([x=1,y=2]:[x:int,y:int],x,2)):[x:int,y:int],
                       R),writeln(R).
  /*
  test(record)  :- test((λ(z,[y=z])$10),
                        (λ(z:int,[y=z])$10):[y:int]).
  test(record)  :- test(λ(z,z#a),
                        λ(z:'%x2',(z:'%x2')#a): ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1')))).
  test(record)  :- test(modify((λ(z,[x=1,y=z])$10),x,2),
                        modify((λ(z:int,[x=1,y=z])$10):[x:int,y:int],x,2):[x:int,y:int]).
  test(variant) :- test({[eint=1]},
                       ({[eint=1]}:'%x0'): ∀('%x0',{[eint:int]},'%x0')).
  test(variant) :- test(case({[eint=1]},{[eint=λ(x,x)]}),
                        case({[eint=1]}:{[eint:int]},{[eint=λ(x:int,x)]}):int).
  test(variant) :- test(case(λ(z,{[eint=z]})$1,{[eint=λ(x,x)]}),
                        case(λ(z:int,{[eint=z]}:{[eint:int]})$1,{[eint=λ(x:int,x)]}):int).
  test(variant) :- test(case(λ(z,{[eint=z]})$1,{[eint=λ(x,x),b=λ(x,x)]}),
                        case(λ(z:int,{[eint=z]}:{[eint:int,b:int]})$1,{[eint=λ(x:int,x),b=λ(x:int,x)]}):int).
  test(let) :- test(let(x=1);x,
                   (let(x:int=poly(1:int));x):int).
  test(let) :- test(let(id=λ(x,x));id,
                   (let(id: ∀('%x0',u,('%x0'->'%x0'))
                          =poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));(id!'%x1'))
                   : ∀('%x1',u,('%x1'->'%x1'))).
  test(let) :- test(let(id=λ(x,x));id$1,
                   (let(id: ∀('%x0',u,('%x0'->'%x0'))
                          =poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));(id!int)$1) : int).
  test(let) :- test(let(id=λ(x,λ(y,x)));id$1$2,
                   (let(id: ∀('%x1',u,∀('%x0',u,('%x0'->'%x1'->'%x0')))
                          = poly(λ(x:'%x0',λ(y:'%x1',x)): ∀('%x1',u,∀('%x0',u,('%x0'->'%x1'->'%x0')))));
                          id!int!int$1$2):int).
  */
:- end_tests(compile).

:- run_tests.
:- halt.
