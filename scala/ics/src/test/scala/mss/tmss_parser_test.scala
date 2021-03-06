package mss
import org.scalatest.FunSpec
import tmss._
import tmss_parser.{parseσ,parsek,parseM}

class tmss_parser_test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  def test[T](a:String,b:T,c:T) = it(a) {assertResult(b)(c)}
  describe("parse q 1") {
    test("x", parseσ("x"),Tx("x"))
    test("b", parseσ("int"),TInt)
    test("fun", parseσ("int->int"),TArr(TInt,TInt))
    test("empty_record", parseσ("{}"),TRecord(List()))
    test("one_element_record", parseσ("{a:int}"),TRecord(List("a"->TInt)))
    test("three_elements_record", parseσ("{a:int,b:int,c:bool}"),TRecord(List("a"->TInt,"b"->TInt,"c"->TBool)))
    test("nested_record", parseσ("{a:int,b:{a:int,c:bool}}"),TRecord(List("a"->TInt,"b"->TRecord(List("a"->TInt,"c"->TBool)))))
    test("variant", parseσ("<eint:int,eadd:{_1:e,_2:e}>"),TVariant(List("eint"->TInt,"eadd"->TRecord(List("_1"->Tx("e"),"_2"->Tx("e"))))))
  }
  describe("parse k") {
    test("k", parsek("U"),U)
    test("k2", parsek("{{}}"),KRecord(List()))
    test("k3", parsek("{{l:int}}"),KRecord(List("l"->TInt)))
    test("k4", parsek("<<eint:int,eadd:{_1:int,_2:int},emul:{_1:int,_2:int}>>"),KVariant(List(
      "eint"->TInt,
      "eadd"->TRecord(List("_1"->TInt,"_2"->TInt)),
      "emul"->TRecord(List("_1"->TInt,"_2"->TInt)))))
  }
  describe("parse q 2") {
    test("q", parseσ("∀t::U.t"),TAll("t",U,Tx("t")))
    test("q2",parseσ("∀t::{{a:int,b:int}}.t"),TAll("t",KRecord(List("a"->TInt,"b"->TInt)),Tx("t")))
    test("q3",parseσ("∀t::<<a:t,b:t>>.<a:t,b:t,c:int>"),TAll("t",KVariant(List("a"->Tx("t"),"b"->Tx("t"))),TVariant(List("a"->Tx("t"),"b"->Tx("t"),"c"->TInt))))
    test("q4",parseσ("∀t::{{a:t,b:t}}.{a:t,b:t,c:int}"),TAll("t",KRecord(List("a"->Tx("t"),"b"->Tx("t"))),TRecord(List("a"->Tx("t"),"b"->Tx("t"),"c"->TInt))))
  }
  describe("parse M") {
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
      assertResult(MAbs("x",Tx("t"),Mx("x")))(
        parseM("λx:t.x"))
    }
    it("app") {
      assertResult(MApp(MAbs("x",Tx("t"),Mx("x")),MInt(1)))(
        parseM("(λx:t.x) 1"))
    }
    it("tapp") {
      assertResult(MTApp(Mx("x"),List(TInt)))(parseM("x!int"))
    }
    it("record") {
      assertResult(MRecord(List("x"->MInt(1),"y"->MInt(2))))(
        parseM("{x=1,y=2}"))
      assertResult(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),
                        TRecord(List("x"->TInt,"y"->TInt)),"x"))(
        parseM("{x=1,y=2}:{x:int,y:int}#x"))
    }
    it("record2") {
      assertResult(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),
                           TRecord(List("x"->TInt,"y"->TInt)),"x",MInt(2)))(
        parseM("modify({x=1,y=2}:{x:int,y:int},x,2)"))
    }
    it("record3") {
      assertResult(MApp(MAbs("z",TInt,MRecord(List("y"->Mx("z")))),MInt(1)))(
        parseM("(λz:int.{y=z}) 1"))
    }
    it("record4") {
      assertResult(MModify(
        MApp(MAbs("z",TInt,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(1)),
        TRecord(List("x"->TInt,"y"->TInt)),"x",MInt(2)))(
        parseM("modify((λz:int.{x=1,y=z}) 1:{x:int,y:int},x,2)"))
    }
    it("variant") {
      assertResult(MVariant("eint",MInt(1),TVariant(List("eint"->TInt,"eadd"->TRecord(List("_1"->TInt,"_2"->TInt))))))(
        parseM("<eint=1>:<eint:int,eadd:{_1:int,_2:int}>"))
    }
    it("variant2") {
      assertResult(
        MCase(MVariant("eint",MInt(1),TVariant(List("eint"->TInt))),
          List("eint"->MAbs("x",TInt,Mx("x"))))
        )(
          parseM("case<eint=1>:<eint:int>of<eint=λx:int.x>")
        )
    }
    it("variant3") {
      assertResult(
        MCase(MApp(MAbs("z",TInt,MVariant("eint",Mx("z"),TVariant(List("eint"->TInt)))),MInt(1)),
          List("eint"->MAbs("x",TInt,Mx("x"))))
      )(
        parseM("case (λz:int.<eint=z>:<eint:int>) 1 of<eint=λx:int.x>")
      )
    }
    it("variant4") {
      assertResult(
        MCase(MApp(MAbs("z",TInt,MVariant("eint",Mx("z"),TVariant(List("eint"->TInt, "b"->TInt)))),MInt(1)),
          List("eint"->MAbs("x",TInt,Mx("x")), "b"->MAbs("x",TInt,Mx("x"))))
      )(
        parseM("case (λz:int.<eint=z>:<eint:int,b:int>) 1 of<eint=λx:int.x,b=λx:int.x>")
      )
    }
    it("let") {
      assertResult(MLet("x",TInt,MPoly(MInt(1),TInt),Mx("x")))(
        parseM("let x:int=Poly(1:int) in x"))
    }
    it("let2") {
      assertResult(MLet("x",TAll("x0",U,TArr(Tx("x0"),Tx("x0"))),
        MPoly(MAbs("x",Tx("x0"),Mx("x")),TAll("x0",U,TArr(Tx("x0"),Tx("x0")))),MTApp(Mx("id"),List(Tx("x1")))))(
        parseM("let x: ∀x0::U.x0->x0=Poly(λx:x0.x:∀x0::U.x0->x0) in id!x1"))
    }
    it("let3") {
      assertResult(MLet("x",TAll("x0",U,TArr(Tx("x0"),Tx("x0"))),
        MPoly(MAbs("x",Tx("x0"),Mx("x")),TAll("x0",U,TArr(Tx("x0"),Tx("x0")))),MApp(MTApp(Mx("id"),List(TInt)),MInt(1))))(
        parseM("let x: ∀x0::U.x0->x0=Poly(λx:x0.x:∀x0::U.x0->x0) in id!int 1"))
    }
  }
}
