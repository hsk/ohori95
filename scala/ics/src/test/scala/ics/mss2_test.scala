package ics
import org.scalatest.FunSpec
import mss2._
import mss2parser.{parseE,parseσ,parsek,parseM}

class mss2_test extends FunSpec {
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
    it("cb") {
      assertResult(esub(Map("x"->Ex("y")),parseE("1")))(parseE("1"))
      assertResult(esub(Map("x"->Ex("y")),parseE("true")))(parseE("true"))
      assertResult(esub(Map("x"->Ex("y")),parseE("false")))(parseE("false"))
    }
    it("x") {
      assertResult(esub(Map("x"->Ex("y")),parseE("x")))(parseE("y"))
      assertResult(esub(Map("x"->Ex("y"),"y"->Ex("z")),parseE("x")))(parseE("z"))
      assertResult(esub(Map("y"->Ex("z"),"x"->Ex("y")),parseE("x")))(parseE("z"))
      assertResult(esub(Map("x"->Ex("y"),"y"->Ex("z")),parseE("x")))(parseE("z"))
      assertResult(esub(Map("y"->Ex("z"),"x"->Ex("y")),parseE("x")))(parseE("z"))
    }
    it("λ") {
      assertResult(esub(Map("x"->Ex("y"),"y"->Ex("z")),parseE("λx.x")))(parseE("λx.x"))
      assertResult(esub(Map("x"->Ex("y"),"y"->Ex("z")),parseE("λa.x")))(parseE("λa.z"))
      assertResult(esub(Map("y"->Ex("z"),"x"->Ex("y")),parseE("λa.x")))(parseE("λa.z"))
    }
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
      assertResult(parseE("1"))(
        eval(parseE("case (λz.<eint=z>) 1 of<eint=λx.x,eadd=λx.add x#_1 x#_2>")))
    }
  }
  describe("eftv") {
    it("a") {
      assertResult(eftv(Map(tx("t1")->U,tx("t2")->parsek("{{l:t1}}")),parseσ("t1")))(Set("t1"))
      assertResult(eftv(Map(tx("t1")->U,tx("t2")->parsek("{{l:t1}}")),parseσ("t2")))(Set("t2","t1"))
    }
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
    def test(A:x,M_ :x,T_ :x) {
      reset()
      val (k,s,m,t) =wk(Map(),Map(),parseE(A))
      //println("test k="+k+" t="+t)
      val (_,t1)=cls(k,Map(),t)
      //println("test t1="+t1)
      val m_ = mtsub(s,m)
      assertResult(parseM(M_))(m_)
      assertResult(parseσ(T_))(t1)
    }
    def tesk(A:x,M_ :x,T_ :x,K_ :Map[σ,k]) {
      reset()
      val (k,s,m,t) =wk(Map(),Map(),parseE(A))
      val (_,t1)=cls(k,Map(),t)
      val m_ = mtsub(s,m)
      assertResult(parseM(M_))(m_)
      assertResult(parseσ(T_))(t1)
      assertResult(K_)(k)
    }

    it("int")     { test("10",   "10",   "int") }
    it("true")    { test("true", "true", "bool") }
    it("false")   { test("false","false","bool") }
    it("λ")       { test("λx.x", "λx:x0.x", "∀x0::U.x0->x0") }
    it("app")     { test(
      "(λx.x) 1",
      "(λx:int.x) 1", "int") }
    it("record")  { test(
      "{x=1,y=2}",
      "{x=1,y=2}","{x:int,y:int}") }
    it("record2") { test(
      "{x=1,y=2}#x",
      "{x=1,y=2}:{x:int,y:int}#x","int") }
    it("record3") { test(
      "{x=1,y=2}#y",
      "{x=1,y=2}:{x:int,y:int}#y","int") }
    it("record4") { test(
      "{x=(λx.x) 1,y=2}#x",
      "{x=(λx:int.x) 1,y=2}:{x:int,y:int}#x","int") }
    it("record5") { test(
      "modify({x=1,y=2},x,2)",
      "modify({x=1,y=2}:{x:int,y:int},x,2)","{x:int,y:int}") }
    it("record6") { test(
      "(λz.{y=z}) 10",
      "(λz:int.{y=z}) 10","{y:int}") }
    it("record7") { tesk(
      "λz.z#a",
      "λz:x2.z:x2#a",
      "∀x1::U.∀x2::{{a:x1}}.x2->x1",
      Map(tx("x1")->U,tx("x2")->parsek("{{a:x1}}"))) }
    it("record8") { test(
      "modify((λz.{x=1,y=z}) 10,x,2)",
      "modify((λz:int.{x=1,y=z}) 10:{x:int,y:int},x,2)",
      "{x:int,y:int}") }
    it("variant") { tesk("<eint=1>",
      "<eint=1>:x0",
      "∀x0::<<eint:int>>.x0",
      Map(tx("x0") -> parsek("<<eint:int>>"))) }
    it("variant2") { test(
      "case <eint=1> of <eint=λx.x>",
      "case <eint=1>:<eint:int> of <eint=λx:int.x>",
      "int") }
    it("variant3") { test(
      "case (λz.<eint=z>) 1 of <eint=λx.x>",
      "case (λz:int.<eint=z>:<eint:int>) 1 of <eint=λx:int.x>",
      "int") }
    it("variant4") { test(
      "case (λz.<eint=z>) 1 of <eint=λx.x,b=λx.x>",
      "case (λz:int.<eint=z>:<eint:int,b:int>) 1 of <eint=λx:int.x,b=λx:int.x>",
      "int") }
    it("let") { test(
      "let x=1 in x",
      "let x:int=Poly(1:int) in x",
      "int") }
    it("let2") { tesk(
      "let id=λx.x in id",
      "let id: ∀x0::U.x0->x0=Poly(λx:x0.x : ∀x0::U.x0->x0) in id!x1",
      "∀x1::U.x1->x1",
      Map(tx("x1")->U)) }
    it("let3") { test(
      "let id=λx.x in id 1",
      "let id:∀x0::U.x0->x0=Poly(λx:x0.x : ∀x0::U.x0->x0) in (id!int) 1",
      "int") }
    it("let4") { test(
      """let id=λx.λy.x in id 1 2""",
      """let id: ∀x0::U.∀x1::U.x0->x1->x0
        |      =Poly(λx:x0.λy:x1.x : ∀x0::U.∀x1::U.x0->x1->x0)
        |in (id!int!int) 1 2""".stripMargin,
      "int") }
    it("let_poly") { tesk(
      """let id = λx.x#a in id""",
      """let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
        |  = Poly(λx:x2.x:x2#a : ∀x1::U.∀x2::{{a:x1}}.x2->x1)
        |                in id!x3!x4""".stripMargin,
      "∀x4::{{a:x3}}.∀x3::U.x4->x3",
      Map(tx("x3")->U,tx("x4")->parsek("{{a:x3}}"))) }
    it("let_poly2") { test(
      """let id=λx.x#a in id {a=10,b=20}""",
      """let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
        |      = Poly(λx:x2.x:x2#a : ∀x1::U.∀x2::{{a:x1}}.x2->x1)
        |            in (id!int!{a:int,b:int}) {a=10,b=20}""".stripMargin,
      "int") }
  }
}
