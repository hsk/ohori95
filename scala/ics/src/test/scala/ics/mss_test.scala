package ics
import org.scalatest.FunSpec
import mss._
import mss_parser.{parseE}

class mss_test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
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
}
