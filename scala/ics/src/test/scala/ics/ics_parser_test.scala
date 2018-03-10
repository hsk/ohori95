package ics
import org.scalatest.FunSpec
import ics._
import ics_parser.{parseC}

class ics_parser_test extends FunSpec {
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
}
