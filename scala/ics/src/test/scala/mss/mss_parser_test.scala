package mss
import org.scalatest.FunSpec
import mss._
import mss_parser.{parseE}

class mss_parser_test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  def test[T](a:String,b:T,c:T) = it(a) {assertResult(b)(c)}
  describe("parse E") {
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
}
