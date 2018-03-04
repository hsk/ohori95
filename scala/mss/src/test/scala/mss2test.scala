import org.scalatest.FunSpec
import mss2._
import mss2parser.{parseE,parseσ,parsek,parseM}

class sos2test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  describe("e") {
    /*
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
    %test(e_kapp) :- e(λ(x::u,x)!int).
    test(e_record) :- e([x=1,y=2]).
    test(e_record) :- e([x=1,y=2]#x).
    test(e_record) :- e(modify([x=1,y=2],x,2)).
    test(e_variant) :- e({[eint=1]}).
    test(e_variant) :- e(case({[eint=1]},{[eint=λ(x,x),eadd=λ(x,add$x#'1'$x#'2')]})),!.
    */
  }
  describe("q1") {
    /*
    test(x) :- q(x).
    test(b) :- q(int).
    test(fun) :- q(int->int).
    test(empty_record):- q([]).
    test(one_element_record):- q([a:int]).
    test(three_elements_record):- q([a:int,b:int,c:bool]).
    test(nested_record):- q([a:int,b:[a:int,c:bool]]).
    test(variant):- q({[eint:int,eadd:['1':e,'2':e]]}).
    */
  }
  describe("k") {
    /*
    test(k):- k(u).
    test(k):- k([]).
    test(k):- k([l:int]).
    test(k):- k({[eint:int,eadd:['1':int,'2':int],emul:['1':int,'2':int]]}),!.
    */
  }
  describe("q2") {
    /*
    test(q):- q(∀(t,u,t)).
    test(q):- q(∀(t,[a:int,b:int],t)).
    test(q):- q(∀(t,{[a:t,b:t]},{[a:t,b:t,c:int]})),!.
    test(q):- q(∀(t,[a:t,b:t],[a:t,b:t,c:int])).
    */
  }
  describe("esub") {
    /*
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
    */
  }
  describe("eval") {
    it("λ") {
      assertResult(parseE("1"))(eval(parseE("(λx.x) 1")))
      assertResult(parseE("10"))(eval(parseE("(λz.z) ((λx.x) 10)")))
    }
    it("record") {
     assertResult(parseE("1"))(eval(parseE("{x=1,y=2}#x")))
     assertResult(parseE("2"))(eval(parseE("{x=1,y=2}#y")))
     assertResult(parseE("1"))(eval(parseE("{x=(λx.x) 1,y=2}#x")))
    }
    it("record2") {
     assertResult(parseE("{x=2,y=2}"))(
       eval(parseE("modify({x=1,y=2},x,2)")))
    }
    it("record3") {
     assertResult(parseE("{y=10}"))(
       eval(parseE("(λz.{y=z}) 10")))
    }
    it("record4") {
     assertResult(parseE("{x=1,y=10}"))(
       eval(parseE("(λz.{x=1,y=z}) ((λx.x) 10)")))
     assertResult(parseE("{x=2,y=10}"))(
       eval(parseE("modify((λz.{x=1,y=z}) 10,x,2)")))
    }
    it("variant") {
     assertResult(parseE("<eint=1>"))(eval(parseE("<eint=1>")))
    }
    it("variant2") {
     assertResult(parseE("1"))(eval(parseE("case (λz.<eint=z>) 1 of<eint=λx.x,eadd=λx.add x#_1 x#_2>")))
    }
  }
  describe("eftv") {
    /*
    test(a) :- eftv([t1 : u, t2 : [l:t1]],t1,R),!,R=[t1].
    test(a) :- eftv([t1 : u, t2 : [l:t1]],t2,R),!,R=[t2,t1].
    */
  }
  describe("cls") {
    /*
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t1,R),!,R=([t2:[l:t1]],∀(t1,u,t1)).
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
    */
  }
  describe("M") {
    test("int",M(MInt(10)))
    /*
    test("true",M(true))
    test("false",M(false))
    test("λ",M(λ(x:'%x0',x)))
    test("app",M(λ(x:int,x)$1))
    %test("app",test("λ(t::u,λ(x:t,x)) , Q),!,Q= ∀(t,u,(t->t)))
    %test("tapp",test("(λ(t::u,λ(x:t,x)) ! int), Q),!,Q=(int->int))
    test("record",'M'([x=1,y=2]))
    test("record",'M'(([x=1,y=2]:[x:int,y:int])#x))
    test("record",'M'(([x=1,y=2]:[x:int,y:int])#y))
    test("record",'M'(([x=λ(x:int,x)$1,y=2]:[x:int,y:int])#x))
    test("record",'M'(modify([x=1,y=2]:[x:int,y:int],x,2)))
    test("record",'M'(λ(z:int,[y=z])$10))
    test("record",'M'(modify((λ(z:int,[x=1,y=z])$10):[x:int,y:int],x,2)))
    test("variant",'M'({[eint=1]}:'%x0'))
    test("variant",'M'(case({[eint=1]}:{[eint:int]},{[eint=λ(x:int,x)]})),!)
    test("variant",'M'(case(λ(z:int,{[eint=z]}:{[eint:int]})$1,{[eint=λ(x:int,x)]})),!)
    test("variant",'M'(case(λ(z:int,{[eint=z]}:{[eint:int,b:int]})$1,{[eint=λ(x:int,x),b=λ(x:int,x)]})),!)
    test("let",'M'((let(x:int=poly(1:int));x)))
    test("let",'M'((let(id: ∀('%x0',u,('%x0'->'%x0'))=poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));id!'%x1')))
    test("let",'M'((let(id: ∀('%x0',u,('%x0'->'%x0'))=poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));id!int$1)))
    */
  }
  describe("typing") {
    /*
    def test("A,(M_:T_)) :- reset,wk([],[],A,(K,S,M,T)),cls(K,[],T,(_,T1)),mtsub(S,M,M_),M(M_),T_=T1,!.
    def test(A,(M_:T_),K_) :- reset,wk([],[],A,(K,S,M,T)),cls(K,[],T,(_,T1)),mtsub(S,M,M_),M(M_),T_=T1,!,K=K_.

    test(int)   :- test(10,   10   :int).
    test(true)  :- test(true, true :bool).
    test(false) :- test(false,false:bool).
    test(λ)     :- test(λ(x,x),
                        λ(x:'%x0',x) : ∀('%x0',u,('%x0'->'%x0'))).
    test(app)   :- test((λ(x,x)$1),
                        (λ(x:int,x)$1): int).
    %test(app)  :- test(λ(t::u,λ(x:t,x)) , ∀(t,u,(t->t)).
    %test(tapp) :- test((λ(t::u,λ(x:t,x)) ! int), int->int).
    test(record) :- test([x=1,y=2],
                        [x=1,y=2]:[x:int,y:int]).
    test(record)  :- test(([x=1,y=2]#x),
                        (([x=1,y=2]:[x:int,y:int])#x):int).
    test(record)  :- test(([x=1,y=2]#y),
                        (([x=1,y=2]:[x:int,y:int])#y):int).
    test(record)  :- test(([x=(λ(x,x)$1),y=2]#x),
                        (([x=λ(x:int,x)$1,y=2]:[x:int,y:int])#x):int).
    test(record)  :- test((modify([x=1,y=2],x,2)),
                          (modify([x=1,y=2]:[x:int,y:int],x,2)):[x:int,y:int]).
    test(record)  :- test((λ(z,[y=z])$10),
                          (λ(z:int,[y=z])$10):[y:int]).
    test(record)  :- test(λ(z,z#a),
                          λ(z:'%x2',(z:'%x2')#a): ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1'))),
                          ['%x1':u,'%x2':[a:'%x1']]).
    test(record)  :- test(modify((λ(z,[x=1,y=z])$10),x,2),
                          modify((λ(z:int,[x=1,y=z])$10):[x:int,y:int],x,2):[x:int,y:int]).
    test(variant) :- test({[eint=1]},
                        ({[eint=1]}:'%x0'): ∀('%x0',{[eint:int]},'%x0'),['%x0':{[eint:int]}]).
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
                    : ∀('%x1',u,('%x1'->'%x1')),
                    ['%x1':u]).
    test(let) :- test(let(id=λ(x,x));id$1,
                    (let(id: ∀('%x0',u,('%x0'->'%x0'))
                            =poly(λ(x:'%x0',x): ∀('%x0',u,('%x0'->'%x0'))));(id!int)$1) : int).
    test(let) :- test(let(id=λ(x,λ(y,x)));id$1$2,
                    (let(id: ∀('%x1',u,∀('%x0',u,('%x0'->'%x1'->'%x0')))
                            = poly(λ(x:'%x0',λ(y:'%x1',x)): ∀('%x1',u,∀('%x0',u,('%x0'->'%x1'->'%x0')))));
                            id!int!int$1$2):int).
    test(let_poly)
      :- test(let(id=λ(x,x#a));id,
              (let(id: ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1')))
                    =poly(λ(x:'%x2',(x:'%x2')#a): ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1')))));
                    id!'%x3'!'%x4'): ∀('%x3',u,∀('%x4',[a:'%x3'],('%x4'->'%x3'))),
              ['%x3':u,'%x4':[a:'%x3']]).
    test(let_poly2)
      :- test(let(id=λ(x,x#a));id$[a=10,b=20],
            (let(id: ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1')))
                    =poly(λ(x:'%x2',(x:'%x2')#a): ∀('%x1',u,∀('%x2',[a:'%x1'],('%x2'->'%x1')))));
                    id!int![a:int,b:int]$[a=10,b=20]):int).
    */
  }
}
