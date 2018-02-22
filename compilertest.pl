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
  test(e_xcb) :- e(1),e(true),e(xxx).
  test(e_λ) :- e(λ(x,x)).
  test(e_app) :- e(λ(x,x)$1).
%  test(e_kapp) :- e(λ(x::u,x)!int).
  test(e_record) :- e([x=1,y=2]).
  test(e_record) :- e([x=1,y=2]#x).
  test(e_record) :- e(modify([x=1,y=2],x,2)).
  test(e_variant) :- e({[eint=1]}).
  test(e_variant) :- e(case({[eint=1]},{[eint=λ(x,x),eadd=λ(x,add$x#'1'$x#'2')]})),!.

  test(c_xcb) :- 'C'(1),'C'(true),'C'(xxx).
  test(c_λ) :- 'C'(λ(x,x)).
  test(c_app) :- 'C'(λ(x,x)$1).
  test(c_λ) :- 'C'(λI(i,i)).
%  test(c_kapp) :- 'C'(λ(x::u,x)!int).
  test(c_record) :- 'C'([1,2]).
  test(c_record) :- 'C'([1,2]#[i]).
  test(c_record) :- 'C'([1,2]#[1]).
  test(c_record) :- 'C'(modify([1,2],1,2)).
  test(c_variant) :- 'C'({[1=1]}).
  test(c_variant) :- 'C'(switch(1,[λ(x,x),λ(x,add$x#[1]$x#[2])])),!.
  
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

/*
  todo:
  test(app) :- m(λ(x:t,x)$1).
  test(kapp) :- m(λ(x::u,x)$int).
  test(record) :- m([x=1,y=2]).
  test(record) :- m([x=1,y=2]#x).
  test(record) :- m(modify([x=1,y=2],x,2)).
  test(variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
*/
:- end_tests(csub).

:- begin_tests(eval).
  test(λ) :- λ(x,x) $ 1 ⟹* 1.
%  test(λ) :- λ(t::u,λ(x:t,x)) ! int ⟹* λ(x:int,x).
%  test(λ) :- λ(t::u,λ(x:t,x)) ! int $ 1 ⟹* 1.
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

:- begin_tests(eftv).
/*
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t1,R),!,R=[t1].
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t2,R),!,R=[t2,t1].
  */
:- end_tests(eftv).

:- begin_tests(cls).
/*
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t1,R),!,R=([t2::[l:t1]],∀(t1,u,t1)).
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
  */
:- end_tests(cls).
/*
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
