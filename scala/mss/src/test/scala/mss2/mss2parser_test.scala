package mss2
import org.scalatest.FunSpec
import mss2._
import mss2parser.{parseE,parseσ,parsek,parseM}
class mss2parser_test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  def test[T](a:String,b:T,c:T) = it(a) {assertResult(b)(c)}
  describe("parseE") {
    it("i") {
      assertResult(EInt(1))(parseE("1"))
      assertResult(EInt(10))(parseE("10"))
      assertResult(EInt(-10))(parseE("-10"))
    }
    it("cb") {
      assertResult(ETrue)(parseE("true"))
      assertResult(EFalse)(parseE("false"))
    }
    it("x") {
      assertResult(Ex("x"))(parseE("x"))
    }
    it("λ") {
      assertResult(EAbs("x",Ex("x")))(parseE("λx.x"))
    }
    it("app") {
      assertResult(EApp(EAbs("x",Ex("x")),EInt(1)))(
        parseE("(λx.x) 1"))
    }
    it("record") {
      assertResult(ERecord(List("x"->EInt(1),"y"->EInt(2))))(
        parseE("{x=1,y=2}"))
      assertResult(EDot(ERecord(List("x"->EInt(1),"y"->EInt(2))),"x"))(
        parseE("{x=1,y=2}#x"))
    }
    it("record2") {
      assertResult(EModify(ERecord(List("x"->EInt(1),"y"->EInt(2))),"x",EInt(2)))(
        parseE("modify({x=1,y=2},x,2)"))
    }
    it("variant") {
      assertResult(EVariant("eint",EInt(1)))(
        parseE("<eint=1>"))
    }
    it("variant2") {
      assertResult(
        ECase(EVariant("eint",EInt(1)),
          List(
            "eint"->EAbs("x",Ex("x")),
            "eadd"->EAbs("x",EApp(EApp(Ex("add"),EDot(Ex("x"),"_1")),EDot(Ex("x"),"_2"))))
          )
        )(
          parseE("""
          case <eint=1> of <
            eint=λx.x,
            eadd=λx.add x#_1 x#_2
          >
          """)
        )
    }
    it("let") {
      assertResult(ELet("x",EInt(1),Ex("x")))(
        parseE("let x=1 in x"))
    }
    it("let2") {
      assertResult(ELet("id",EAbs("x",Ex("x")),EApp(Ex("id"),EInt(1))))(
        parseE("let id= λx.x in id 1"))
    }
  }
  describe("q1") {
    test("x", parseσ("x"),tx("x"))
    test("b", parseσ("int"),tint)
    test("fun", parseσ("int->int"),tarr(tint,tint))
    test("empty_record", parseσ("{}"),trecord(List()))
    test("one_element_record", parseσ("{a:int}"),trecord(List("a"->tint)))
    test("three_elements_record", parseσ("{a:int,b:int,c:bool}"),trecord(List("a"->tint,"b"->tint,"c"->tbool)))
    test("nested_record", parseσ("{a:int,b:{a:int,c:bool}}"),trecord(List("a"->tint,"b"->trecord(List("a"->tint,"c"->tbool)))))
    test("variant", parseσ("<eint:int,eadd:{_1:e,_2:e}>"),tvariant(List("eint"->tint,"eadd"->trecord(List("_1"->tx("e"),"_2"->tx("e"))))))
  }
  describe("k") {
    test("k", parsek("U"),U)
    test("k2", parsek("{{}}"),krecord(List()))
    test("k3", parsek("{{l:int}}"),krecord(List("l"->tint)))
    test("k4", parsek("<<eint:int,eadd:{_1:int,_2:int},emul:{_1:int,_2:int}>>"),kvariant(List(
      "eint"->tint,
      "eadd"->trecord(List("_1"->tint,"_2"->tint)),
      "emul"->trecord(List("_1"->tint,"_2"->tint)))))
  }
  describe("q2") {
    test("q", parseσ("∀t::U.t"),∀("t",U,tx("t")))
    test("q2",parseσ("∀t::{{a:int,b:int}}.t"),∀("t",krecord(List("a"->tint,"b"->tint)),tx("t")))
    test("q3",parseσ("∀t::<<a:t,b:t>>.<a:t,b:t,c:int>"),∀("t",kvariant(List("a"->tx("t"),"b"->tx("t"))),tvariant(List("a"->tx("t"),"b"->tx("t"),"c"->tint))))
    test("q4",parseσ("∀t::{{a:t,b:t}}.{a:t,b:t,c:int}"),∀("t",krecord(List("a"->tx("t"),"b"->tx("t"))),trecord(List("a"->tx("t"),"b"->tx("t"),"c"->tint))))
  }
  describe("parseM") {
    it("i") {
      assertResult(MInt(1))(parseM("1"))
      assertResult(MInt(10))(parseM("10"))
      assertResult(MInt(-10))(parseM("-10"))
    }
    it("cb") {
      assertResult(MTrue)(parseM("true"))
      assertResult(MFalse)(parseM("false"))
    }
    it("x") {
      assertResult(Mx("x"))(parseM("x"))
    }
    it("λ") {
      assertResult(MAbs("x",tx("t"),Mx("x")))(
        parseM("λx:t.x"))
    }
    it("app") {
      assertResult(MApp(MAbs("x",tx("t"),Mx("x")),MInt(1)))(
        parseM("(λx:t.x) 1"))
    }
    //test("app",test("λ(t::u,λ(x:t,x)) , Q),!,Q= ∀(t,u,(t->t)))
    //test("tapp",test("(λ(t::u,λ(x:t,x)) ! int), Q),!,Q=(int->int))
    it("tapp") {
      assertResult(MTApp(Mx("x"),tint))(parseM("x!int"))
    }
    it("record") {
      assertResult(MRecord(List("x"->MInt(1),"y"->MInt(2))))(
        parseM("{x=1,y=2}"))
      assertResult(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),
                        trecord(List("x"->tint,"y"->tint)),"x"))(
        parseM("{x=1,y=2}:{x:int,y:int}#x"))
    }
    it("record2") {
      assertResult(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),
                           trecord(List("x"->tint,"y"->tint)),"x",MInt(2)))(
        parseM("modify({x=1,y=2}:{x:int,y:int},x,2)"))
    }
    it("record3") {
      assertResult(MApp(MAbs("z",tint,MRecord(List("y"->Mx("z")))),MInt(1)))(
        parseM("(λz:int.{y=z}) 1"))
    }
    it("record4") {
      assertResult(MModify(
        MApp(MAbs("z",tint,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(1)),
        trecord(List("x"->tint,"y"->tint)),"x",MInt(2)))(
        parseM("modify((λz:int.{x=1,y=z}) 1:{x:int,y:int},x,2)"))
    }
    it("variant") {
      assertResult(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("_1"->tint,"_2"->tint))))))(
        parseM("<eint=1>:<eint:int,eadd:{_1:int,_2:int}>"))
    }
    it("variant2") {
      assertResult(
        MCase(MVariant("eint",MInt(1),tvariant(List("eint"->tint))),
          List("eint"->MAbs("x",tint,Mx("x"))))
        )(
          parseM("case<eint=1>:<eint:int>of<eint=λx:int.x>")
        )
    }
    it("variant3") {
      assertResult(
        MCase(MApp(MAbs("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint)))),MInt(1)),List("eint"->MAbs("x",tint,Mx("x"))))
      )(
        parseM("case (λz:int.<eint=z>:<eint:int>) 1 of<eint=λx:int.x>")
      )
    }
    it("variant4") {
      assertResult(
        MCase(MApp(MAbs("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint, "b"->tint)))),MInt(1)),List("eint"->MAbs("x",tint,Mx("x")), "b"->MAbs("x",tint,Mx("x"))))
      )(
        parseM("case (λz:int.<eint=z>:<eint:int,b:int>) 1 of<eint=λx:int.x,b=λx:int.x>")
      )
    }
    it("let") {
      assertResult(MLet("x",tint,MPoly(MInt(1),tint),Mx("x")))(
        parseM("let x:int=Poly(1:int) in x"))
    }
    it("let2") {
      assertResult(MLet("x",∀("x0",U,tarr(tx("x0"),tx("x0"))),
        MPoly(MAbs("x",tx("x0"),Mx("x")),∀("x0",U,tarr(tx("x0"),tx("x0")))),MTApp(Mx("id"),tx("x1"))))(
        parseM("let x: ∀x0::U.x0->x0=Poly(λx:x0.x:∀x0::U.x0->x0) in id!x1"))
    }
    it("let3") {
      assertResult(MLet("x",∀("x0",U,tarr(tx("x0"),tx("x0"))),
        MPoly(MAbs("x",tx("x0"),Mx("x")),∀("x0",U,tarr(tx("x0"),tx("x0")))),MApp(MTApp(Mx("id"),tint),MInt(1))))(
        parseM("let x: ∀x0::U.x0->x0=Poly(λx:x0.x:∀x0::U.x0->x0) in id!int 1"))
    }
  }

  /*
  describe("eval") {
    def evalt(src:String,result:String):Boolean = eval(parseE(src))==parseE(result)
    test("λ", evalt("(λx:int.x) 1","1"))
    test("λ2", evalt("(λt::U.λx:t.x)!int","λx:int.x"))
    test("λ3", evalt("(λt::U.λx:t.x)!int 1","1"))
    test("record", evalt("{x=1,y=2}#x","1"))
    test("record2", evalt("{x=1,y=2}#y","2"))
    test("record3", evalt("{x=(λx:int.x) 1,y=2}#x","1"))
    test("record4", evalt("modify({x=1,y=2},x,10)","{x=10,y=2}"))
    test("record5", evalt("(λz:int.{y=z}) 10","{y=10}"))
    test("record6", evalt("modify((λz:tint.{x=1,y=z}) 10,x,2)","{x=2,y=10}"))
    test("variant", evalt("<eint=1>:<eint:int,eadd:{_1:int,_2:int}>","<eint=1>:<eint:int,eadd:{_1:int,_2:int}>"))
    test("variant2", evalt("""
      case (λz:int.<eint=z>:<eint:int,eadd:{_1:int,_2:int}>) 1 of <
        eint=λx:int.x,
        eadd=λx:int.add (x#_1) (x#_2)
      >
    """, "1"))
  }

  describe("typing") {
    def ti2(m:String,σ:String):Boolean = ti(Map(),Map(),parseE(m)) == parseσ(σ)
    test("int", ti2("10","int"))
    test("true", ti2("true","bool"))
    test("false", ti2("false","bool"))
    test("λ", ti2("λx:int.x","int->int"))
    test("app", ti2("(λx:int.x) 1","int"))
    test("tabs", ti2("λt::U.λx:t.x", "∀t::U.t->t"))
    test("tapp", ti2("(λt::U.λx:t.x)!int", "int->int"))
    test("record", ti2("{x=2,y=2}","{x:int,y:int}"))
    test("record2", ti2("{x=1,y=2}#x","int"))
    test("record3", ti2("{x=1,y=2}#y","int"))
    test("record4", ti2("{x=(λx:int.x) 1,y=2}#x","int"))
    test("record5", ti2("modify({x=1,y=2},x,2)","{x:int,y:int}"))
    test("record6", ti2("(λz:int.{y=z}) 10","{y:int}"))
    test("record7", ti2("modify((λz:int.{x=1,y=z}) 10,x,2)","{x:int,y:int}"))
    test("variant", ti2("<eint=1>:<eint:int,eadd:{_1:int,_2:int}>","<eint:int,eadd:{_1:int,_2:int}>"))
    test("variant2", ti2("case (λz:int.<eint=z>:<eint:int>) 1 of <eint=λx:int.x>","int"))
    test("variant3", ti2("case (λz:int.<eint=z>:<eint:int,b:int>) 1 of <eint=λx:int.x,b=λx:int.x>","int"))
  }
  */
}
