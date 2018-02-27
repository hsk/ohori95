:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(tmss).

:- set_prolog_flag(allow_variable_name_as_functor,true). % M(a) と書ける。

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
  test(m_xcb) :- M(1),M(true),M(xxx![]),M(xxx![int]).
  test(m_λ) :- M(λ(x:int,x![])).
  test(m_app) :- M(λ(x:int,x![])$1).
%  test(m_kapp) :- M(λ(x::u,x)!int).
  test(m_poly) :- M(poly([x=y![]]: ∀(a,u,[x:a]))).
  test(m_let) :- M(let(r: ∀(a,u,[x:a])=poly([x=y![]]: ∀(a,u,[x:a])));r![int]).
  test(m_record) :- M([x=1,y=2]).
  test(m_record) :- M(([x=1,y=2]:[x:int,y:int])#x).
  test(m_record) :- M(modify([x=1,y=2]:[x:int,y:int],x,2)).
  test(m_variant) :- M({[eint=1]}:{[eint:int]}).
  test(m_variant) :- M(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[
    eint=λ(x:int,x![]),
    eadd=λ(x:['1':int,'2':int],
      add![] $ ((x![]):['1':int,'2':int])#'1'
             $ ((x![]):['1':int,'2':int])#'2'
    )
  ]})),!.

:- end_tests(avs).

:- begin_tests(q1).
  test(x) :- q(x).
  test(b) :- q(int).
  test(fun) :- q(int->int).
  test(empty_record):- q([]).
  test(one_element_record):- q([a:int]).
  test(three_elements_record):- q([a:int,b:int,c:bool]).
  test(nested_record):- q([a:int,b:[a:int,c:bool]]).
  test(variant):- q({[eint:int,eadd:['1':e,'2':e]]}).
:- end_tests(q1).

:- begin_tests(k).
  test(k):- k(u).
  test(k):- k([]).
  test(k):- k([l::int]).
  test(k):- k({[eint::int,eadd::['1':int,'2':int],emul::['1':int,'2':int]]}),!.
:- end_tests(k).

:- begin_tests(q2).
  test(q):- q(∀(t,u,t)).
  test(q):- q(∀(t,[a::int,b::int],t)).
  test(q):- q(∀(t,{[a::t,b::t]},{[a:t,b:t,c:int]})),!.
  test(q):- q(∀(t,[a::t,b::t],[a:t,b:t,c:int])).
:- end_tests(q2).

:- begin_tests(msub).
  test(cb) :- msub([y/x],1,1),msub([y/x],true,true),msub([y/x],false,false),!.
  test(x) :- msub([y/x],x,y),!.
  test(x) :- msub([y/x,z/y],x,z),!.
  test(x) :- msub([z/y,y/x],x,z),!.
  test(x) :- msub([y/x,z/y],x,z),!.
  test(x) :- msub([z/y,y/x],x,z),!.
  test('x![]') :- msub([y/x],x![],y![]),!.
  test(λ) :- msub([y/x,z/y],λ(x:t,x),λ(x:t,x)),!.
  test(λ) :- msub([y/x,z/y],λ(a:t,x),λ(a:t,z)),!.
  test(λ) :- msub([z/y,y/x],λ(a:t,x),λ(a:t,z)),!.

  test(app) :- msub([a/x],λ(x:t,x)$1,λ(x:t,x)$1),!.
  test(app) :- msub([a/y],λ(x:t,y)$1,λ(x:t,a)$1),!.
%  test(kapp) :- m(λ(x::u,x)$int).
/*
  todo:
  test(record) :- m([x=1,y=2]).
  test(record) :- m([x=1,y=2]#x).
  test(record) :- m(modify([x=1,y=2],x,2)).
  test(variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
*/
:- end_tests(msub).

:- begin_tests(eval).
  test(λ) :- λ(x:int,x) $ 1 ⟹* 1.
  %test(λ) :- λ(t::u,λ(x:t,x)) ! int ⟹* λ(x:int,x).
  %test(λ) :- λ(t::u,λ(x:t,x)) ! int $ 1 ⟹* 1.
  test(record) :- ([x=1,y=2]#x) ⟹* 1.
  test(record) :- ([x=1,y=2]#y) ⟹* 2.
  test(record) :- ([x=(λ(x:int,x)$1),y=2]#x) ⟹* 1.
  test(record) :- (modify([x=1,y=2],x,2)) ⟹* [x=2,y=2].
  test(record) :- (λ(z:int,[y=z])$10) ⟹* [y=10].
  /*
  test(record) :- (modify(λ(z:int,[x=1,y=z])$10,x,2)) ⟹* R,!,R=[x=2,y=10].
  test(variant) :- ({[eint=1]}) ⟹* ({[eint=1]}).
  test(variant) :- (case((λ(z:int,{[eint=z]})$1),{[eint=λ(x:int,x),eadd=λ(x:['1':int,'2':int],add$x#'1'$x#'2')]})) ⟹* 1.
  */
:- end_tests(eval).

/*
:- begin_tests(eftv).
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t1,R),!,R=[t1].
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t2,R),!,R=[t2,t1].
:- end_tests(eftv).

:- begin_tests(cls).
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t1,R),!,R=([t2::[l:t1]],∀(t1,u,t1)).
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
:- end_tests(cls).

test(A,(M_,T_)) :- reset,wk([],[],A,(K,S,M,T)),cls(K,[],T,(_,T_)),mtsub(S,M,M_).
:- begin_tests(typing).
  test(int) :- test(10,Q),!,Q=(10,int).
  test(true) :- test(true,Q),!,Q=(true,bool).
  test(false) :- test(false,Q),!,Q=(false,bool).
  test(λ) :- test(λ(x,x), Q),!,Q=(λ(x:'%x0',x),∀('%x0',u,('%x0'->'%x0'))).
  test(app) :- test((λ(x,x)$1), Q),!,Q=(λ(x:int,x)$1,int).
%  test(app) :- test(λ(t::u,λ(x:t,x)) , Q),!,Q= ∀(t,u,(t->t)).
%  test(tapp) :- test((λ(t::u,λ(x:t,x)) ! int), Q),!,Q=(int->int).
  test(record) :- test(([x=1,y=2]), Q),!,Q=([x=1,y=2],[x:int,y:int]).

  test(record) :- test(([x=1,y=2]#x), Q),!,Q=(([x=1,y=2]:[x:int,y:int])#x,int).
  test(record) :- test(([x=1,y=2]#y), Q),!,Q=(([x=1,y=2]:[x:int,y:int])#y,int).
  test(record) :- test(([x=(λ(x,x)$1),y=2]#x), Q),!,Q==(([x=λ(x:int,x)$1,y=2]:[x:int,y:int])#x,int).
  test(record) :- test((modify([x=1,y=2],x,2)), Q),!,Q==(modify([x=1,y=2]:[x:int,y:int],x,2),[x:int,y:int]).
  test(record) :- test((λ(z,[y=z])$10), Q),!,Q==(λ(z:int,[y=z])$10,[y:int]).
  test(record) :- test((modify((λ(z,[x=1,y=z])$10),x,2)), Q),!,Q==(modify((λ(z:int,[x=1,y=z])$10):[x:int,y:int],x,2),[x:int,y:int]).
  test(variant) :- test({[eint=1]},Q),!,Q==({[eint=1]}:'%x0',∀('%x0',{[eint:int]},'%x0')).
  test(variant) :- test((case({[eint=1]},{[eint=λ(x,x)]})),Q),!,Q==(case({[eint=1]}:{[eint:int]},{[eint=λ(x:int,x)]}),int).
  test(variant) :- test((case((λ(z,{[eint=z]})$1),{[eint=λ(x,x)]})),Q),!,Q==(case(λ(z:int,{[eint=z]}:{[eint:int]})$1,{[eint=λ(x:int,x)]}),int).
  test(variant) :- test((case((λ(z,{[eint=z]})$1),{[eint=λ(x,x),b=λ(x,x)]})),Q),!,Q==(case(λ(z:int,{[eint=z]}:{[eint:int,b:int]})$1,{[eint=λ(x:int,x),b=λ(x:int,x)]}),int).
  test(let) :- test(let(x=1);x,Q),!,Q==((let(x:int=poly(1:int));x),int).
  test(let) :- test(let(id=λ(x,x));id,Q),!,
    Q=((let(id: ∀('%x0',u,('%x0'->'%x0'))=poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));x(id,'%x1')),∀('%x1',u,('%x1'->'%x1'))).
  test(let) :- test(let(id=λ(x,x));id$1,Q),!,
    Q=((let(id: ∀('%x0',u,('%x0'->'%x0'))=poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));x(id,int)$1),int).

:- end_tests(typing).
*/
:- run_tests.
:- halt.
