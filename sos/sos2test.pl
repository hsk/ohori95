:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(sos2).

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
  test(m_xcb) :- m(1),m(true),m(xxx).
  test(m_λ) :- m(λ(x:t,x)).
  test(m_app) :- m(λ(x:t,x)$1).
  test(m_kapp) :- m(λ(x::u,x)!int).
  test(m_record) :- m([x=1,y=2]).
  test(m_record) :- m([x=1,y=2]#x).
  test(m_record) :- m(modify([x=1,y=2],x,2)).
  test(m_variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(m_variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
  
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
  test(k):- k([l:int]).
  test(k):- k({[eint:int,eadd:['1':int,'2':int],emul:['1':int,'2':int]]}),!.
:- end_tests(k).

:- begin_tests(q2).
  test(q):- q(∀(t,u,t)).
  test(q):- q(∀(t,[a:int,b:int],t)).
  test(q):- q(∀(t,{[a:t,b:t]},{[a:t,b:t,c:int]})),!.
  test(q):- q(∀(t,[a:t,b:t],[a:t,b:t,c:int])).
:- end_tests(q2).

:- begin_tests(msub).
  test(cb) :- msub([y/x],1,1),msub([y/x],true,true),msub([y/x],false,false).
  test(x) :- msub([y/x],x,y).
  test(x) :- msub([y/x,z/y],x,z).
  test(x) :- msub([z/y,y/x],x,z).
  test(x) :- msub([y/x,z/y],x,z).
  test(x) :- msub([z/y,y/x],x,z).
  test(λ) :- msub([y/x,z/y],λ(x:t,x),λ(x:t,x)).
  test(λ) :- msub([y/x,z/y],λ(a:t,x),λ(a:t,z)).
  test(λ) :- msub([z/y,y/x],λ(a:t,x),λ(a:t,z)).
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
:- end_tests(msub).

:- begin_tests(eval).
  test(λ) :- λ(x:int,x) $ 1 ⟹* 1.
  test(λ) :- λ(t::u,λ(x:t,x)) ! int ⟹* λ(x:int,x).
  test(λ) :- λ(t::u,λ(x:t,x)) ! int $ 1 ⟹* 1.
  test(record) :- ([x=1,y=2]#x) ⟹* 1.
  test(record) :- ([x=1,y=2]#y) ⟹* 2.
  test(record) :- ([x=(λ(x:int,x)$1),y=2]#x) ⟹* 1.
  test(record) :- (modify([x=1,y=2],x,2)) ⟹* [x=2,y=2].
  test(record) :- (λ(z:int,[y=z])$10) ⟹* [y=10].
  test(record) :- (modify((λ(z:int,[x=1,y=z])$10),x,2)) ⟹* [x=2,y=10].  
  test(variant) :- ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}) ⟹* ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
  test(variant) :- (case((λ(z:int,{[eint=z]}:{[eint:int,eadd:['1':int,'2':int]]})$1),{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})) ⟹* 1.
:- end_tests(eval).

:- begin_tests(typing).
  test(int) :- ([],[]) ▷ 10 : Q,!,Q=int.
  test(true) :- ([],[]) ▷ true : Q,!,Q=bool.
  test(false) :- ([],[]) ▷ false : Q,!,Q=bool.
  test(λ) :- ([],[]) ▷ λ(x:int,x) : Q,!,Q==(int->int).
  test(app) :- ([],[]) ▷ (λ(x:int,x)$1) : Q,!,Q=int.
  test(app) :- ([],[]) ▷ λ(t::u,λ(x:t,x))  : Q,!,Q= ∀(t,u,(t->t)).
  test(tapp) :- ([],[]) ▷ (λ(t::u,λ(x:t,x)) ! int) : Q,!,Q=(int->int).
  test(record) :- ([],[]) ▷ ([x=1,y=2]) : Q,!,Q=[x:int,y:int].
  test(record) :- ([],[]) ▷ ([x=1,y=2]#x) : Q,!,Q=int.
  test(record) :- ([],[]) ▷ ([x=1,y=2]#y) : Q,!,Q=int.
  test(record) :- ([],[]) ▷ ([x=(λ(x:int,x)$1),y=2]#x): Q, !,Q==int.
  test(record) :- ([],[]) ▷ (modify([x=1,y=2],x,2)) : Q,!,Q==[x:int,y:int] .
  test(record) :- ([],[]) ▷ (λ(z:int,[y=z])$10) : Q,!,Q==[y:int].
  test(record) :- ([],[]) ▷ (modify((λ(z:int,[x=1,y=z])$10),x,2)) : Q,!,Q==[x:int,y:int].
  test(variant) :- ([],[]) ▷ ({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}) : Q,!, Q=={[eint:int,eadd:['1':int,'2':int]]}.
  test(variant) :- ([],[]) ▷ (case((λ(z:int,{[eint=z]}:{[eint:int]})$1),{[eint=λ(x:int,x)]})) : Q,!,Q==int.
  test(variant) :- ([],[]) ▷ (case((λ(z:int,{[eint=z]}:{[eint:int,b:int]})$1),{[eint=λ(x:int,x),b=λ(x:int,x)]})) : Q,!,Q==int.
:- end_tests(typing).

:- run_tests.
:- halt.
