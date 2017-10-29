:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(mss).

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

:- begin_tests(esub).
  test(cb) :- esub([y/x],1,1),esub([y/x],true,true),esub([y/x],false,false).
  test(x) :- esub([y/x],x,y).
  test(x) :- esub([y/x,z/y],x,z).
  test(x) :- esub([z/y,y/x],x,z).
  test(x) :- esub([y/x,z/y],x,z).
  test(x) :- esub([z/y,y/x],x,z).
  test(λ) :- esub([y/x,z/y],λ(x,x),λ(x,x)).
  test(λ) :- esub([y/x,z/y],λ(a,x),λ(a,z)).
  test(λ) :- esub([z/y,y/x],λ(a,x),λ(a,z)).
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
:- end_tests(esub).

:- begin_tests(eval).
  test(λ) :- λ(x,x) $ 1 ⟹* 1.
%  test(λ) :- λ(t::u,λ(x:t,x)) ! int ⟹* λ(x:int,x).
%  test(λ) :- λ(t::u,λ(x:t,x)) ! int $ 1 ⟹* 1.
  test(record) :- ([x=1,y=2]#x) ⟹* 1.
  test(record) :- ([x=1,y=2]#y) ⟹* 2.
  test(record) :- ([x=(λ(x,x)$1),y=2]#x) ⟹* 1.
  test(record) :- (modify([x=1,y=2],x,2)) ⟹* [x=2,y=2].
  test(record) :- (λ(z,[y=z])$10) ⟹* [y=10].
  test(record) :- (modify((λ(z,[x=1,y=z])$10),x,2)) ⟹* R,!,R=[x=2,y=10].  
  test(variant) :- ({[eint=1]}) ⟹* ({[eint=1]}).
  test(variant) :- (case((λ(z,{[eint=z]})$1),{[eint=λ(x,x),eadd=λ(x,add$x#'1'$x#'2')]})) ⟹* 1.
:- end_tests(eval).

:- begin_tests(eftv).
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t1,R),!,R=[t1].
  test(a) :- eftv([t1 :: u, t2 :: [l:t1]],t2,R),!,R=[t2,t1].
:- end_tests(eftv).

:- begin_tests(cls).
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t1,R),!,R=([t2::[l:t1]],∀(t1,u,t1)).
  test(a) :- cls([t1 :: u, t2 :: [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
:- end_tests(cls).

test(A,(M,T_)) :- reset,wk([],[],A,(K,_,M,T)),cls(K,[],T,(_,T_)).
:- begin_tests(typing).
  test(int) :- test(10,Q),!,Q=(10,int).
  test(true) :- test(true,Q),!,Q=(true,bool).
  test(false) :- test(false,Q),!,Q=(false,bool).
  test(λ) :- test(λ(x,x), Q),!,writeln(q=Q),Q=(λ(x:'%x0',x),∀('%x0',u,('%x0'->'%x0'))).
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
  %test(variant) :- writeln(-----),test((case({[eint=1]},{[eint=λ(x,x)]})),Q),!,writeln(q=Q),Q==int.
  %test(variant) :- writeln(-----),test((case((λ(z,{[eint=z]})$1),{[eint=λ(x,x)]})),Q),!,writeln(q=Q),Q==int.
  %test(variant) :- test((case((λ(z,{[eint=z]})$1),{[eint=λ(x,x),b=λ(x,x)]})),Q),!,writeln(q=Q),Q==int.
:- end_tests(typing).

:- run_tests.
:- halt.
