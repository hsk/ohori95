:- expects_dialect(sicstus).
:- current_prolog_flag(argv, [V]), use_module(V)
  ; use_module(rics).

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

:- end_tests(eval).

:- begin_tests(τ).
  test(x) :- τ(x).
  test(b) :- τ(int).
  test(fun) :- τ(int->int).
  test(empty_record):- τ([]).
  test(one_element_record):- τ([a:int]).
  test(three_elements_record):- τ([a:int,b:int,c:bool]).
  test(nested_record):- τ([a:int,b:[a:int,c:bool]]).
  test(idx) :- τ(idx(a,x,int)). % todo
:- end_tests(τ).

:- begin_tests(k).
  test(k):- k(u).
  test(k):- k([]).
  test(k):- k([l::int]).
:- end_tests(k).

:- begin_tests(σ).
  test(σ):- σ(∀(t,u,t)).
  test(σ):- σ(∀(t,[a::int,b::int],t)).
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
:- end_var_names(_).
:- end_tests(kinding).

:- begin_tests(index_judgment).
  test('IVAR I') :- [k:idx(x,int)] ⊢ k : idx(x,int),!.
  test('IVAR i record') :- [] ⊢ 1 : idx(k,[k:int,j:int]),!.
  test('IVAR i record') :- [] ⊢ 2 : idx(j,[k:int,j:int]),!.
:- end_tests(index_judgment).

:- begin_tests(typing).
  test(var) :- ([],[],[xxx:int]) ▷ xxx : T,!,T=int.
  test(true) :- ([],[],[]) ▷ true : B,!,B=bool.
  test(false) :- ([],[],[]) ▷ false : B,!,B=bool.
  test(1) :- ([],[],[]) ▷ 1 : B,!,B=int.
  test(app) :- ([],[],[f:(int->int)]) ▷ (f $ 1) : B,!,B=int.
  test(λ) :- ([],[],[]) ▷ λ(x,x) : B,!,B=(C->C).
  test(λ) :- ([],[],[f:(int->int)]) ▷ λ(x,f $ x) : B,!,B\=(bool->bool),B=(int->int).

  /*test(A,(M_,T_)) :- reset,wk([],[],A,(K,S,M,T)),cls(K,[],T,(_,T_)),mtsub(S,M,M_).
  test(int) :- test(10,Q),!,Q=(10,int).
  test(true) :- test(true,Q),!,Q=(true,bool).
  test(false) :- test(false,Q),!,Q=(false,bool).
  test(λ) :- test(λ(x,x), Q),!,Q=(λ(x:'%x0',x),∀('%x0',u,('%x0'->'%x0'))).
  test(app) :- test((λ(x,x)$1), Q),!,Q=(λ(x:int,x)$1,int).
  % test(app) :- test(λ(t::u,λ(x:t,x)) , Q),!,Q= ∀(t,u,(t->t)).
  % test(tapp) :- test((λ(t::u,λ(x:t,x)) ! int), Q),!,Q=(int->int).
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
*/
  test(record) :- ([],[],[]) ▷ [10,20] : T,writeln(t:T).
  test(index) :- ([],[],[]) ▷ ([10,true]#[1]) : int.
  test(index) :- ([],[],[]) ▷ ([10,true]#[2]) : bool.
  test(modify) :- ([],[],[]) ▷ (modify([11,22],2,10)) : T,T=[_:int,_:int].
  test(let) :- ([],[],[]) ▷ (let(x=1);x) : B,!,B=int.
:- end_tests(typing).


:- run_tests.
:- halt.
