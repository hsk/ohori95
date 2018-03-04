import org.scalatest.FunSpec
import sos2._

class sos2test extends FunSpec {
  def test(a:String,b:Boolean) = it(a) {assert(b)}
  describe("avs") {
    it("i") {assert(i(MInt(1)))}
    it("i2") {assert(i(MInt(10)))}
    it("i3") {assert(i(MInt(-10)))}
    it("cb") {assert(cb(MInt(-10)))}
    it("cb2") {assert(cb(MTrue))}
    it("cb3") {assert(cb(MFalse))}
    it("x") {assert(x(Mx("x")))}
    it("x2") {assert(!x(MTrue))}
    it("x3") {assert(!x(MInt(1)))}
    it("m_xcb") {assert(m(MInt(1)) && m(MTrue) && m(Mx("xxx")))}
    it("m_λ") {assert(m(Mλ("x",tx("t"),Mx("x"))))}
    it("m_app") {assert(m(MApp(Mλ("x",tx("t"),Mx("x")),MInt(1))))}
    it("m_kapp") {assert(m(MTλ("x",U,MTApp(Mx("x"),tint))))}
    it("m_record") {assert(m(MRecord(List("x"->MInt(1),"y"->MInt(2)))))}
    it("m_record2") {assert(m(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x")))}
    it("m_record3") {assert(m(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(2))))}
    it("m_variant") {assert(m(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))))}
    it("m_variant2") {assert(m(MCase(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2")))))))}
  }
  describe("q1") {
    test("x", q(tx("x")))
    test("b", q(tint))
    test("fun", q(tarr(tint,tint)))
    test("empty_record", q(trecord(List())))
    test("one_element_record", q(trecord(List("a"->tint))))
    test("three_elements_record", q(trecord(List("a"->tint,"b"->tint,"c"->tbool))))
    test("nested_record", q(trecord(List("a"->tint,"b"->trecord(List("a"->tint,"c"->tbool))))))
    test("variant", q(tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tx("e"),"2"->tx("e")))))))
  }
  describe("k") {
    test("k", k(U))
    test("k2", k(krecord(List())))
    test("k3", k(krecord(List("l"->tint))))
    test("k4", k(kvariant(List(
      "eint"->tint,
      "eadd"->trecord(List("1"->tint,"2"->tint)),
      "emul"->trecord(List("1"->tint,"2"->tint))))))
  }
  describe("q2") {
    test("q", q(∀("t",U,tx("t"))))
    test("q2", q(∀("t",krecord(List("a"->tint,"b"->tint)),tx("t"))))
    test("q3", q(∀("t",kvariant(List("a"->tx("t"),"b"->tx("t"))),tvariant(List("a"->tx("t"),"b"->tx("t"),"c"->tint)))))
    test("q4", q(∀("t",krecord(List("a"->tx("t"),"b"->tx("t"))),trecord(List("a"->tx("t"),"b"->tx("t"),"c"->tint)))))
  }
  describe("msub") {
    test("cb", msub(Map("x"->Mx("y")),MInt(1))==MInt(1))
    test("cb2", msub(Map("x"->Mx("y")),MTrue)==MTrue)
    test("cb3", msub(Map("x"->Mx("y")),MFalse)==MFalse)
    test("x", msub(Map("x"->Mx("y")),Mx("x"))==Mx("y"))
    test("x2", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mx("x"))==Mx("z"))
    test("x3", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mx("x"))==Mx("z"))
    test("x4", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mx("x"))==Mx("z"))
    test("x5", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mx("x"))==Mx("z"))
    test("λ", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mλ("x",tx("t"),Mx("x")))==Mλ("x",tx("t"),Mx("x")))
    test("λ2", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mλ("a",tx("t"),Mx("x")))==Mλ("a",tx("t"),Mx("z")))
    test("λ3", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mλ("a",tx("t"),Mx("x")))==Mλ("a",tx("t"),Mx("z")))
    test("app", msub(Map("x"->Mx("y")),MApp(Mλ("x",tx("t"),Mx("x")),Mx("x")))==MApp(Mλ("x",tx("t"),Mx("x")),Mx("y")))
    test("app2", msub(Map("x"->Mx("y"),"a"->Mx("b")),MApp(Mλ("a",tx("t"),Mx("x")),Mx("a")))==MApp(Mλ("a",tx("t"),Mx("y")),Mx("b")))
    test("kapp", msub(Map("x"->Mx("y")),MTApp(MTλ("x",U,Mx("x")),tint))==MTApp(MTλ("x",U,Mx("y")),tint))
    test("record", msub(Map("x"->Mx("z")),MRecord(List("x"->Mx("x"),"y"->MInt(2))))==MRecord(List("x"->Mx("z"),"y"->MInt(2))))
    test("record2", msub(Map("x"->Mx("z")),MDot(MRecord(List("x"->Mx("x"),"y"->MInt(2))),"x"))==MDot(MRecord(List("x"->Mx("z"),"y"->MInt(2))),"x"))
    test("record3", msub(Map("x"->Mx("z")),MModify(MRecord(List("x"->Mx("x"),"y"->MInt(2))),"x",Mx("x")))==MModify(MRecord(List("x"->Mx("z"),"y"->MInt(2))),"x",Mx("z")))
    test("variant", msub(Map("x"->Mx("z")),MVariant("eint",Mx("x"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))==
      MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))
    test("variant2", msub(Map("x"->Mx("z")),MCase(MVariant("eint",Mx("x"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2"))))))==
    MCase(MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2"))))))
  }
  describe("eval") {
    test("λ", eval(MApp(Mλ("x",tint,Mx("x")),MInt(1))) == MInt(1))
    test("λ2", eval(MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint)) == Mλ("x",tint,Mx("x")))
    test("λ3", eval(MApp(MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint),MInt(1))) == MInt(1))
    test("record", eval(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x"))==MInt(1))
    test("record2", eval(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"y"))==MInt(2))
    test("record3", eval(MDot(MRecord(List("x"->MApp(Mλ("x",tint,Mx("x")),MInt(1)),"y"->MInt(2))),"x"))==MInt(1))
    test("record4", eval(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(10)))==MRecord(List("x"->MInt(10),"y"->MInt(2))))
    test("record5", eval(MApp(Mλ("z",tint,MRecord(List("y"->Mx("z")))),MInt(10)))==MRecord(List("y"->MInt(10))))
    test("record6", eval(MModify(MApp(Mλ("z",tint,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(10)),"x",MInt(2)))==MRecord(List("x"->MInt(2),"y"->MInt(10))))
    test("variant", eval(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))) == MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))

    test("variant2", eval(MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MDot(Mx("x"),"1"),MDot(Mx("x"),"2")))))) == MInt(1))
  }
  describe("typing") {
    test("int", ti(Map(),Map(),MInt(10))==tint)
    test("true", ti(Map(),Map(),MTrue)==tbool)
    test("false", ti(Map(),Map(),MFalse)==tbool)
    test("λ", ti(Map(),Map(),Mλ("x",tint,Mx("x")))==tarr(tint,tint))
    test("app", ti(Map(),Map(),MApp(Mλ("x",tint,Mx("x")),MInt(1)))==tint)
    test("tabs", ti(Map(),Map(),MTλ("t",U,Mλ("x",tx("t"),Mx("x"))))== ∀("t",U,tarr(tx("t"),tx("t"))))
    test("tapp", ti(Map(),Map(),MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint))==tarr(tint,tint))
    test("record", ti(Map(),Map(),MRecord(List("x"->MInt(1),"y"->MInt(2))))==trecord(List("x"->tint,"y"->tint)))
    test("record2", ti(Map(),Map(),MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x"))==tint)
    test("record3", ti(Map(),Map(),MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"y"))==tint)
    test("record4", ti(Map(),Map(),MDot(MRecord(List("x"->MApp(Mλ("x",tint,Mx("x")),MInt(1)),"y"->MInt(2))),"x"))==tint)
    test("record5", ti(Map(),Map(),MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(2)))==trecord(List("x"->tint,"y"->tint)))
    test("record6", ti(Map(),Map(),MApp(Mλ("z",tint,MRecord(List("y"->Mx("z")))),MInt(10)))==trecord(List("y"->tint)))
    test("record7", ti(Map(),Map(),MModify(MApp(Mλ("z",tint,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(10)),"x",MInt(2)))==trecord(List("x"->tint,"y"->tint)))
    test("variant", ti(Map(),Map(),MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))) == tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))
    test("variant2", ti(Map(),Map(),MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint)))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")))))==tint)
    test("variant3", ti(Map(),Map(),MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"b"->tint)))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")),"b"->Mλ("x",tint,Mx("x")))))==tint)
  }

  // Free Type variables
  def ftv(σ:σ):Set[x] = σ match {
    case tx(x) => Set(x)
    case _ if b(σ) => Set()
    case tarr(σ1,σ2) => ftv(σ1)++ftv(σ2)
    case trecord(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case tvariant(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case ∀(t,k,σ) => kftv(k)++ftv(σ) - t
  }
  def kftv(k:k):Set[x] = k match {
    case U => Set()
    case krecord(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case kvariant(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
  }
  def tftv(T:Map[x,σ]):Set[x] =
    T.foldLeft(Set[x]()){case(tv,(_,σ))=>tv++ftv(σ)}
}
