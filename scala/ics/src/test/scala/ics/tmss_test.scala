package ics
import org.scalatest.FunSpec
import mss._
import tmss._
import mss_parser.{parseE}
import tmss_parser.{parseM, parsek, parseσ}

class tmss_test extends FunSpec {

  describe("eftv") {
    it("a") {
      assertResult(eftv(Map(Tx("t1")->U,Tx("t2")->parsek("{{l:t1}}")),parseσ("t1")))(Set("t1"))
      assertResult(eftv(Map(Tx("t1")->U,Tx("t2")->parsek("{{l:t1}}")),parseσ("t2")))(Set("t2","t1"))
    }
  }
  describe("cls") {
    /*
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t1,R),!,R=([t2:[l:t1]],∀(t1,u,t1)).
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
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
    def tesk(A:x,M_ :x,T_ :x,K_ :Map[q,k]) {
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
      Map(Tx("x1")->U,Tx("x2")->parsek("{{a:x1}}"))) }
    it("record8") { test(
      "modify((λz.{x=1,y=z}) 10,x,2)",
      "modify((λz:int.{x=1,y=z}) 10:{x:int,y:int},x,2)",
      "{x:int,y:int}") }
    it("record9") { test(
      "(λa.{k=a#x,j=a#y}){x=1,y=2}",
      "(λa:{x:int,y:int}.{k=a:{x:int,y:int}#x,j=a:{x:int,y:int}#y}){x=1,y=2}",
      "{k:int,j:int}" ) }
    /*
    Expected MApp(MAbs(a,trecord(List((x,tint), (y,tint))),MRecord(List((k,MDot(Mx(a),trecord(List((x,tint), (y,tint))),x)),
      (j,MDot(Mx(a),trecord(List((x,tint), (y,tint))),y))))),MRecord(List((x,MInt(1)), (y,MInt(2)))))
    but got  MApp(MAbs(a,trecord(List((x,tint), (y,tint))),MRecord(List((k,MDot(Mx(a),trecord(List((x,tint), (y,tint))),x)),
      (j,MDot(MTApp(Mx(a),tx(x3)),tx(x3),y))))),MRecord(List((x,MInt(1)), (y,MInt(2)))))
    */
    it("variant") { tesk("<eint=1>",
      "<eint=1>:x0",
      "∀x0::<<eint:int>>.x0",
      Map(Tx("x0") -> parsek("<<eint:int>>"))) }
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
    it("variant5") { test(
      "case <x={a=1}> of <x=λy.y#a>",
      "case <x={a=1}>:<x:{a:int}> of <x=λy:{a:int}.y:{a:int}#a>",
      "int") }
    /*
    Expected MCase(MVariant(x,MRecord(List((a,MInt(1)))),tvariant(List((x,trecord(List((a,tint))))))),
      List((x,MAbs(y,trecord(List((a,tint))),MDot(Mx(y),trecord(List((a,tint))),a))))),
    but got MCase(MVariant(x,MRecord(List((a,MInt(1)))),tvariant(List((x,trecord(List((a,tint))))))),
      List((x,MAbs(y,tx(x3),MDot(Mx(y),tx(x3),a)))))
    */
    it("let") { test(
      "let x=1 in x",
      "let x:int=Poly(1:int) in x",
      "int") }
    it("let2") { tesk(
      "let id=λx.x in id",
      "let id: ∀x0::U.x0->x0=Poly(λx:x0.x : ∀x0::U.x0->x0) in id!x1",
      "∀x1::U.x1->x1",
      Map(Tx("x1")->U)) }
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
      Map(Tx("x3")->U,Tx("x4")->parsek("{{a:x3}}"))) }
    it("let_poly2") { test(
      """let id=λx.x#a in id {a=10,b=20}""",
      """let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
        |      = Poly(λx:x2.x:x2#a : ∀x1::U.∀x2::{{a:x1}}.x2->x1)
        |            in (id!int!{a:int,b:int}) {a=10,b=20}""".stripMargin,
      "int") }
  }
}
