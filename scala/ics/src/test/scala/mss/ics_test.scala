package mss
import org.scalatest.FunSpec
import tmss._
import ics._
import tmss_parser.{parseσ,parsek,parseM}
import ics_parser.{parseC}

class ics_test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  describe("parse C") {
    it("i") {
      assertResult(CInt(1))(parseC("1"))
      assertResult(CInt(10))(parseC("10"))
      assertResult(CInt(-10))(parseC("-10"))
    }
    it("cb") {
      assertResult(CTrue)(parseC("true"))
      assertResult(CFalse)(parseC("false"))
    }
    it("x") {
      assertResult(Cx("x"))(parseC("x"))
    }
    it("λ") {
      assertResult(CAbs("x",Cx("x")))(parseC("λx.x"))
    }
    it("app") {
      assertResult(CApp(CAbs("x",Cx("x")),CInt(1)))(
        parseC("(λx.x) 1"))
    }
    it("record") {
      assertResult(CRecord(List(CInt(1),CInt(2))))(
        parseC("{1,2}"))
      assertResult(CDot(CRecord(List(CInt(1),CInt(2))),CInt(1)))(
        parseC("{1,2}[1]"))
    }
    it("record2") {
      assertResult(CModify(CRecord(List(CInt(1),CInt(2))),CInt(1),CInt(2)))(
        parseC("modify({1,2},1,2)"))
    }
    it("variant") {
      assertResult(CVariant(CInt(1),CInt(1)))(
        parseC("<1=1>"))
    }
    it("variant2") {
      assertResult(
        CSwitch(CVariant(CInt(1),CInt(1)),
          List(
            CAbs("x",Cx("x")),
            CAbs("x",CApp(CApp(Cx("add"),CDot(Cx("x"),CInt(1))),CDot(Cx("x"),CInt(2)))))
          )
        )(
          parseC("""
          switch <1=1> of
            λx.x,
            λx.add (x[1]) (x[2])
          """)
        )
    }
    it("let") {
      assertResult(CLet("x",CInt(1),Cx("x")))(
        parseC("let x=1 in x"))
    }
    it("let2") {
      assertResult(CLet("id",CAbs("x",Cx("x")),CApp(Cx("id"),CInt(1))))(
        parseC("let id= λx.x in id 1"))
    }
  }
  describe("csub") {
    it("cb") {
      assertResult(csub(Map("x"->Cx("y")),parseC("1")))(parseC("1"))
      assertResult(csub(Map("x"->Cx("y")),parseC("true")))(parseC("true"))
      assertResult(csub(Map("x"->Cx("y")),parseC("false")))(parseC("false"))
    }
    it("x") {
      assertResult(csub(Map("x"->Cx("y")),parseC("x")))(parseC("y"))
      assertResult(csub(Map("x"->Cx("y"),"y"->Cx("z")),parseC("x")))(parseC("z"))
      assertResult(csub(Map("y"->Cx("z"),"x"->Cx("y")),parseC("x")))(parseC("z"))
      assertResult(csub(Map("x"->Cx("y"),"y"->Cx("z")),parseC("x")))(parseC("z"))
      assertResult(csub(Map("y"->Cx("z"),"x"->Cx("y")),parseC("x")))(parseC("z"))
    }
    it("λ") {
      assertResult(csub(Map("x"->Cx("y"),"y"->Cx("z")),parseC("λx.x")))(parseC("λx.x"))
      assertResult(csub(Map("x"->Cx("y"),"y"->Cx("z")),parseC("λa.x")))(parseC("λa.z"))
      assertResult(csub(Map("y"->Cx("z"),"x"->Cx("y")),parseC("λa.x")))(parseC("λa.z"))
    }
  }
  describe("eval") {
    it("λ") {
      assertResult(parseC("1"))(ics.eval(parseC("(λx.x) 1")))
      assertResult(parseC("10"))(ics.eval(parseC("(λz.z) ((λx.x) 10)")))
    }
    it("record") {
      assertResult(parseC("10"))(ics.eval(parseC("{10,20}[1]")))
      assertResult(parseC("20"))(ics.eval(parseC("{10,20}[2]")))
      assertResult(parseC("11"))(ics.eval(parseC("{(λx.x) 11,2}[1]")))
      assertResult(parseC("22"))(ics.eval(parseC("{(λx.x) 11,(λy.y) 22}[2]")))
    }
    it("record modify") {
      assertResult(parseC("{10,22}"))(
        ics.eval(parseC("modify({11,22},1,10)")))
      assertResult(parseC("{11,10}"))(
        ics.eval(parseC("modify({11,22},2,10)")))
    }
    it("record app") {
      assertResult(parseC("{10}"))(
        ics.eval(parseC("(λz.{z}) 10")))
    }
    it("record4") {
      assertResult(parseC("{11,10}"))(
        ics.eval(parseC("(λz.{11,z}) ((λx.x) 10)")))
      assertResult(parseC("{22,10}"))(
        ics.eval(parseC("modify((λz.{11,z}) 10,1,22)")))
    }
    it("variant") {
      assertResult(parseC("<1=1>"))(ics.eval(parseC("<1=1>")))
    }
    it("variant2") {
      assertResult(parseC("1"))(
        ics.eval(parseC("switch (λz.<1=z>) 1 of λx.x,λx.add x[1] x[2]")))
    }
    it("variant3") {
      assertResult(parseC("{10,1}"))(
        ics.eval(parseC("switch (λz.<2={z,10}>) 1 of λx.x,λx.{x[2],x[1]}")))
    }
  }
  describe("kinding") {
    /*
    test(kinding_int):- [] ⊢ int:k,k=u,!.
    test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[x:int],!.
    test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[x:int,y:int],!.
    % test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[y:int]. todo
    % test(kinding_record):- [] ⊢ [x:int,y:int]:k,k=[x:int],!.
    test(kinding_record):- [] ⊢ [x:int,y:int]:k,k=[x:int,y:int],!.
    test(kinding_variant_t):- [a:{[x:int,y:int]}] ⊢ a:k,k={[x:int]},!.
    test(kinding_variant_t):- [a:{[x:int,y:int]}] ⊢ a:k,k={[x:int,y:int]},!.
    % test(kinding_variant):- [] ⊢ {[x:int,y:int]}:k,k={[x:int]},!.
    test(kinding_variant):- [] ⊢ {[x:int,y:int]}:k,k={[x:int,y:int]},!.
    */
  }
  describe("index_judgment") {
    /*
    test('IVAR I') :- [k:idx(x,int)] ⊢ k : idx(x,int),!.
    test('IVAR i record') :- [] ⊢ 1 : idx(k,[k:int,j:int]),!.
    test('IVAR i record') :- [] ⊢ 2 : idx(j,[k:int,j:int]),!.
    test('IVAR i variant') :- [] ⊢ 1 : idx(k,{[k:int,j:int]}),!.
    test('IVAR i variant') :- [] ⊢ 2 : idx(j,{[k:int,j:int]}),!.
    */
  }
  describe("*") {
    it("getT") { assertResult(sortq(parseσ("∀t2::{{b:int,a:bool}}.∀t3::{{a:t2}}.t2->t3")))(
      (List("t2"->parsek("{{a:bool,b:int}}"),"t3"->parsek("{{a:t2}}")),parseσ("t2->t3"))) }
    it("rep") { assertResult(
      addIdx(parseσ("∀t2::{{b:int,a:bool}}.∀t3::{{a:t2}}.t2->t3")))(
             parseσ("∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.idx(a,t2)=>idx(b,t2)=>idx(a,t3)=>t2->t3")) }
    it("rep2") { assertResult(addIdx(parseσ("∀x2::{{a:x1}}.x2->x1")))(
                                     parseσ("∀x2::{{a:x1}}.idx(a,x2)=>x2->x1")) }
    it("rep3") { assertResult(addIdx(parseσ("∀x1::U.∀x2::{{a:x1}}.x2->x1")))(
                                     parseσ("∀x1::U.∀x2::{{a:x1}}.idx(a,x2)=>x2->x1")) }
    it("rep4") { assertResult(addIdx(parseσ("∀x2::{{a:x1}}.x2->x1")))(
                                     parseσ("∀x2::{{a:x1}}.idx(a,x2)=>x2->x1")) }
    it("rep5") { assertResult(addIdx(parseσ("∀x1::U.∀x2::{{a:x1}}.x2->x1")))(
                                     parseσ("∀x1::U.∀x2::{{a:x1}}.idx(a,x2)=>x2->x1")) }
  }
  describe("compile") {
    def test(e:x,m:x,t:x,cx:x) {
      assertResult(parseC(cx))(c(List(),Map(),parseM(m)))
    }
    def tesk(e:x, m:x, t:x, K:Map[q,k], cx:x) {
      assertResult(parseC(cx))(c(lk(K),Map(),parseM(m)))
    }
    it("int")        { test("10",   "10"   ,"int" ,"10") }
    it("true")       { test("true", "true" ,"bool","true") }
    it("false")      { test("false","false","bool","false") }
    it("λ")          { test("λ(x,x)",
                            "λx:x0.x", "∀x0::U.x0->x0",
                            "λx.x") }
    it("app")        { test("(λx.x) 1",
                            "(λx:int.x) 1","int",
                            "(λx.x) 1") }
    it("record")     { test("{x=10,y=20}",
                            "{x=10,y=20}","{x:int,y:int}",
                            "{10,20}") }
    it("record 2")   { test("{x=10,y=20}#x",
                            "{x=10,y=20}:{x:int,y:int}#x","int",
                            "{10,20}[1]") }
    it("record 3")   { test("{x=10,y=20}#y",
                            "{x=10,y=20}:{x:int,y:int}#y","int",
                            "{10,20}[2]") }
    it("record 4")   { test("{x=(λx.x) 1,y=2}#x",
                            "{x=(λx:int.x) 1,y=2}:{x:int,y:int}#x","int",
                            "{(λx.x) 1,2}[1]") }
    it("record 5")   { test("modify({x=10,y=20},x,30)",
                            "modify({x=10,y=20}:{x:int,y:int},x,30)","{x:int,y:int}",
                            "modify({10,20},1,30)") }
    it("record 6")   { test("(λz.{y=z}) 10",
                            "(λz:int.{y=z}) 10","{y:int}",
                            "(λz.{z}) 10") }
    it("record 7")   { reset(2)
                       tesk("λz.z#a",
                            "λz:x2.z:x2#a","∀x1::U.∀x2::{{a:x1}}.x2->x1",
                            Map(Tx("x1")->U,Tx("x2")->parsek("{{a:x1}}")),
                            "λz.z[x2]") }
    it("record 8")   { test("modify((λz.{x=1,y=z}) 10,x,2)",
                            "modify((λz:int.{x=1,y=z}) 10:{x:int,y:int},x,2)","{x:int,y:int}",
                            "modify((λz.{1,z}) 10,1,2)") }
    it("variant")    { reset(3)
                       tesk("<eint=1>",
                            "(<eint=1>:x0)","∀(x0,<eint:int>,x0)",
                            Map(Tx("x0")->parsek("<<eint:int>>")),
                            "<x3=1>") }
    it("variant 2")  { test("case<eint=1>of<eint=λx.x>",
                            "case<eint=1>:<eint:int>of<eint=λx:int.x>","int",
                            "switch <1=1> of λx.x") }
    it("variant 3")  { test("case(λz.<eint=z>) 1 of<eint=λx.x>",
                            "case(λz:int.<eint=z>:<eint:int>) 1 of<eint=λx:int.x>","int",
                            "switch(λz.<1=z>) 1 of λx.x") }
    it("variant 4")  { test("case(λz.<eint=z>) 1 of<eint=λx.x,b=λx.x>",
                            "case(λz:int.<eint=z>:<eint:int,b:int>) 1 of<eint=λx:int.x,b=λx:int.x>","int",
                            "switch(λz.<1=z>) 1 of λx.x,λx.x") }
    it("let")        { test("let x=1 in x",
                            "let x:int=Poly(1:int) in x","int",
                            "let x=1 in x") }
    it("let 2")      {
      tesk("let id=λx.x));id",
         """let id:∀x0::U.x0->x0
                  =Poly(λx:x0.x : ∀x0::U.x0->x0) in id!x1""", "∀x1::U.x1->x1",
            Map(Tx("x1")->U),
           "let id=λx.x in id") }
    it("let 3")      {
      test("let id=λx.x in id 1",
         """let id:∀x0::U.x0->x0
                  =Poly(λx:x0.x : ∀x0::U.x0->x0) in (id!int) 1""","int",
           "let id=λx.x in id 1") }
    it("let 4")      {
      test("let id=λx.λy.x in id 1 2",
         """let id: ∀x1::U.∀x0::U.x0->x1->x0
                  = Poly(λx:x0.λy:x1.x : ∀x1::U.∀x0::U.x0->x1->x0) in
                  (id!int!int) 1 2""","int",
           "let id=λx.λy.x in id 1 2") }
    it("let_poly")   {
      reset(5)
      tesk("let id=λx.x#a in id",
         """let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
                    =Poly(λx:x2.x:x2#a: ∀x1::U.∀x2::{{a:x1}}.x2->x1) in
                    id!x3!x4""", "∀x3::U.∀x4::{{a:x3}}.x4->x3",
            Map(Tx("x3")->U,Tx("x4")->parsek("{{a:x3}}")),
           "let id=λx6.λx.x[x6] in id x5") }
    it("let_poly 2") {
      reset(3)
      test("let id=λx.x#a in id {a=10,b=20}",
         """let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
                  =Poly(λx:x2.x:x2#a: ∀x1::U.∀x2::{{a:x1}}.x2->x1) in
                  id!int!{a:int,b:int} {a=10,b=20}""","int",
           "let id=λx3.λx.x[x3] in id 1 {10,20}") }
  }
}
