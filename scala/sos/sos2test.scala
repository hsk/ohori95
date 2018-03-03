import sos2._

object sos2test extends App {
  def test(s:String,b:Boolean) { assert(b) }

  // begin_tests(avs).
  test("i", i(MInt(1)))
  test("i", i(MInt(10)))
  test("i", i(MInt(-10)))
  test("cb", cb(MInt(-10)))
  test("cb", cb(MTrue))
  test("cb", cb(MFalse))
  test("x", x(Mx("x")))
  test("x", !x(MTrue))
  test("x", !x(MInt(1)))
  test("m_xcb", m(MInt(1)) && m(MTrue) && m(Mx("xxx")))
  test("m_λ", m(Mλ("x",tx("t"),Mx("x"))))
  test("m_app", m(MApp(Mλ("x",tx("t"),Mx("x")),MInt(1))))
  test("m_kapp", m(MTλ("x",U,MTApp(Mx("x"),tint))))
  test("m_record", m(MRecord(List("x"->MInt(1),"y"->MInt(2)))))
  test("m_record", m(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x")))
  test("m_record", m(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(2))))
  test("m_variant", m(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))))
  test("m_variant", m(MCase(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2")))))))
  // end_tests(avs).

  // begin_tests(q1).
  test("x", q(tx("x")))
  test("b", q(tint))
  test("fun", q(tarr(tint,tint)))
  test("empty_record", q(trecord(List())))
  test("one_element_record", q(trecord(List("a"->tint))))
  test("three_elements_record", q(trecord(List("a"->tint,"b"->tint,"c"->tbool))))
  test("nested_record", q(trecord(List("a"->tint,"b"->trecord(List("a"->tint,"c"->tbool))))))
  test("variant", q(tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tx("e"),"2"->tx("e")))))))
  // end_tests(q1).

  // begin_tests(k).
  test("k", k(U))
  test("k", k(krecord(List())))
  test("k", k(krecord(List("l"->tint))))
  test("k", k(kvariant(List(
    "eint"->tint,
    "eadd"->trecord(List("1"->tint,"2"->tint)),
    "emul"->trecord(List("1"->tint,"2"->tint))))))
  // end_tests(k).

  // begin_tests(q2).
  test("q", q(∀("t",U,tx("t"))))
  test("q", q(∀("t",krecord(List("a"->tint,"b"->tint)),tx("t"))))
  test("q", q(∀("t",kvariant(List("a"->tx("t"),"b"->tx("t"))),tvariant(List("a"->tx("t"),"b"->tx("t"),"c"->tint)))))
  test("q", q(∀("t",krecord(List("a"->tx("t"),"b"->tx("t"))),trecord(List("a"->tx("t"),"b"->tx("t"),"c"->tint)))))
  // end_tests(q2).

  // begin_tests(msub).
  test("cb", msub(Map("x"->Mx("y")),MInt(1))==MInt(1))
  test("cb", msub(Map("x"->Mx("y")),MTrue)==MTrue)
  test("cb", msub(Map("x"->Mx("y")),MFalse)==MFalse)
  test("x", msub(Map("x"->Mx("y")),Mx("x"))==Mx("y"))
  test("x", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mx("x"))==Mx("z"))
  test("x", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mx("x"))==Mx("z"))
  test("x", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mx("x"))==Mx("z"))
  test("x", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mx("x"))==Mx("z"))
  test("λ", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mλ("x",tx("t"),Mx("x")))==Mλ("x",tx("t"),Mx("x")))
  test("λ", msub(Map("x"->Mx("y"),"y"->Mx("z")),Mλ("a",tx("t"),Mx("x")))==Mλ("a",tx("t"),Mx("z")))
  test("λ", msub(Map("y"->Mx("z"),"x"->Mx("y")),Mλ("a",tx("t"),Mx("x")))==Mλ("a",tx("t"),Mx("z")))
  test("app", msub(Map("x"->Mx("y")),MApp(Mλ("x",tx("t"),Mx("x")),Mx("x")))==MApp(Mλ("x",tx("t"),Mx("x")),Mx("y")))
  test("app", msub(Map("x"->Mx("y"),"a"->Mx("b")),MApp(Mλ("a",tx("t"),Mx("x")),Mx("a")))==MApp(Mλ("a",tx("t"),Mx("y")),Mx("b")))
  test("kapp", msub(Map("x"->Mx("y")),MTApp(MTλ("x",U,Mx("x")),tint))==MTApp(MTλ("x",U,Mx("y")),tint))
  test("record", msub(Map("x"->Mx("z")),MRecord(List("x"->Mx("x"),"y"->MInt(2))))==MRecord(List("x"->Mx("z"),"y"->MInt(2))))
  test("record", msub(Map("x"->Mx("z")),MDot(MRecord(List("x"->Mx("x"),"y"->MInt(2))),"x"))==MDot(MRecord(List("x"->Mx("z"),"y"->MInt(2))),"x"))
  test("record", msub(Map("x"->Mx("z")),MModify(MRecord(List("x"->Mx("x"),"y"->MInt(2))),"x",Mx("x")))==MModify(MRecord(List("x"->Mx("z"),"y"->MInt(2))),"x",Mx("z")))
  test("variant", msub(Map("x"->Mx("z")),MVariant("eint",Mx("x"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))==
    MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))
  test("variant", msub(Map("x"->Mx("z")),MCase(MVariant("eint",Mx("x"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2"))))))==
  MCase(MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MApp(Mx("add"),MDot(Mx("x"),"1")),MDot(Mx("x"),"2"))))))
  // end_tests(msub).

  // begin_tests(eval).
  test("λ", eval(MApp(Mλ("x",tint,Mx("x")),MInt(1))) == MInt(1))
  test("λ", eval(MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint)) == Mλ("x",tint,Mx("x")))
  test("λ", eval(MApp(MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint),MInt(1))) == MInt(1))
  test("record", eval(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x"))==MInt(1))
  test("record", eval(MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"y"))==MInt(2))
  test("record", eval(MDot(MRecord(List("x"->MApp(Mλ("x",tint,Mx("x")),MInt(1)),"y"->MInt(2))),"x"))==MInt(1))
 test("record", eval(MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(10)))==MRecord(List("x"->MInt(10),"y"->MInt(2))))
  test("record", eval(MApp(Mλ("z",tint,MRecord(List("y"->Mx("z")))),MInt(10)))==MRecord(List("y"->MInt(10))))
  test("record", eval(MModify(MApp(Mλ("z",tint,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(10)),"x",MInt(2)))==MRecord(List("x"->MInt(2),"y"->MInt(10))))
  test("variant", eval(MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))) == MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint))))))

  test("variant", eval(MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")),"eadd"->Mλ("x",tint,MApp(MDot(Mx("x"),"1"),MDot(Mx("x"),"2")))))) == MInt(1))
  // end_tests(eval).
 
  // begin_tests(typing).
  test("int", ti(Map(),Map(),MInt(10))==tint)
  test("true", ti(Map(),Map(),MTrue)==tbool)
  test("false", ti(Map(),Map(),MFalse)==tbool)
  test("λ", ti(Map(),Map(),Mλ("x",tint,Mx("x")))==tarr(tint,tint))
  test("app", ti(Map(),Map(),MApp(Mλ("x",tint,Mx("x")),MInt(1)))==tint)
  test("tabs", ti(Map(),Map(),MTλ("t",U,Mλ("x",tx("t"),Mx("x"))))== ∀("t",U,tarr(tx("t"),tx("t"))))
  test("tapp", ti(Map(),Map(),MTApp(MTλ("t",U,Mλ("x",tx("t"),Mx("x"))),tint))==tarr(tint,tint))
  test("record", ti(Map(),Map(),MRecord(List("x"->MInt(1),"y"->MInt(2))))==trecord(List("x"->tint,"y"->tint)))
  test("record", ti(Map(),Map(),MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x"))==tint)
  test("record", ti(Map(),Map(),MDot(MRecord(List("x"->MInt(1),"y"->MInt(2))),"y"))==tint)
  test("record", ti(Map(),Map(),MDot(MRecord(List("x"->MApp(Mλ("x",tint,Mx("x")),MInt(1)),"y"->MInt(2))),"x"))==tint)
  test("record", ti(Map(),Map(),MModify(MRecord(List("x"->MInt(1),"y"->MInt(2))),"x",MInt(2)))==trecord(List("x"->tint,"y"->tint)))
  test("record", ti(Map(),Map(),MApp(Mλ("z",tint,MRecord(List("y"->Mx("z")))),MInt(10)))==trecord(List("y"->tint)))
  test("record", ti(Map(),Map(),MModify(MApp(Mλ("z",tint,MRecord(List("x"->MInt(1),"y"->Mx("z")))),MInt(10)),"x",MInt(2)))==trecord(List("x"->tint,"y"->tint)))
  test("variant", ti(Map(),Map(),MVariant("eint",MInt(1),tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))) == tvariant(List("eint"->tint,"eadd"->trecord(List("1"->tint,"2"->tint)))))
  test("variant", ti(Map(),Map(),MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint)))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")))))==tint)
  test("variant", ti(Map(),Map(),MCase(MApp(Mλ("z",tint,MVariant("eint",Mx("z"),tvariant(List("eint"->tint,"b"->tint)))),MInt(1)),List("eint"->Mλ("x",tint,Mx("x")),"b"->Mλ("x",tint,Mx("x")))))==tint)
  // end_tests(typing).
}
