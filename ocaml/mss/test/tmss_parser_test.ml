open OUnit
open Tmss_lexer
open Mss
open Tmss

let parseq1 () =
  "parse q 1" >::: [
    "x" >:: begin fun () -> assert_equal (parseq "x") (Tx "x") end;
    "b" >:: begin fun () -> assert_equal (parseq "int") TInt end;
    "fun" >:: begin fun () ->
      assert_equal (parseq "int->int") (TArr(TInt,TInt))
    end;
    (*"empty_record" >:: begin fun () ->
      assert_equal (parseq "{}") (TRecord [])
    end;*)
    "one_element_record" >:: begin fun () ->
      assert_equal (parseq "{a:int}") (TRecord ["a",TInt])
    end;
    "three_elements_record" >:: begin fun () ->
      assert_equal (parseq "{a:int,b:int,c:bool}") (TRecord ["a",TInt;"b",TInt;"c",TBool])
    end;
    "nested_record" >:: begin fun () ->
      assert_equal (parseq "{a:int,b:{a:int,c:bool}}")
        (TRecord ["a",TInt;"b",TRecord ["a",TInt;"c",TBool]])
    end;
    "variant" >:: begin fun () ->
      assert_equal (parseq "<eint:int,eadd:{_1:e,_2:e}>")
        (TVariant ["eint",TInt;"eadd",TRecord ["_1",Tx "e";"_2",Tx "e"]])
    end;
  ]
let parsek () =
  "parse k">::: [
    "k"  >:: begin fun () -> assert_equal (parsek "U") U end;
    (*"k2" >:: begin fun () -> assert_equal (parsek "{{}}") (KRecord []) end;*)
    "k3" >:: begin fun () -> assert_equal (parsek "{{l:int}}") (KRecord ["l",TInt]) end;
    "k4" >:: begin fun () ->
      assert_equal
        (parsek "<<eint:int,eadd:{_1:int,_2:int},emul:{_1:int,_2:int}>>")
        (KVariant [
          "eint",TInt;
          "eadd",TRecord ["_1",TInt;"_2",TInt];
          "emul",TRecord ["_1",TInt;"_2",TInt];])
    end;
  ]
let parseq2 () =
  "parse q 2" >::: [
    "q" >:: begin fun () ->
      assert_equal (parseq "∀t::U.t") (TAll("t",U,Tx "t"))
    end;
    "q2" >:: begin fun () ->
      assert_equal (parseq "∀t::{{a:int,b:int}}.t")
        (TAll("t",KRecord ["a",TInt;"b",TInt],Tx "t"))
    end;
    "q3" >:: begin fun () ->
      assert_equal (parseq "∀t::<<a:t,b:t>>.<a:t,b:t,c:int>")
        (TAll("t",KVariant ["a",Tx "t" ;"b",Tx "t"],TVariant ["a",Tx "t";"b",Tx "t";"c",TInt]))
    end;
    "q4" >:: begin fun () ->
      assert_equal (parseq "∀t::{{a:t,b:t}}.{a:t,b:t,c:int}")
        (TAll("t",KRecord ["a",Tx "t";"b",Tx "t"],TRecord ["a",Tx "t";"b",Tx "t";"c",TInt]))
    end;
  ]
let parseM () =
  "parse M" >::: [
    "i" >:: begin fun () ->
      assert_equal (MInt(1))(parseM "1");
      assert_equal (MInt(10))(parseM "10");
      assert_equal (MInt(-10))(parseM "-10");
    end;
    "cb" >:: begin fun () ->
      assert_equal (MTrue)(parseM "true");
      assert_equal (MFalse)(parseM "false");
    end;
    "x" >:: begin fun () ->
      assert_equal (Mx("x"))(parseM "x")
    end;
    "λ" >:: begin fun () ->
      assert_equal (MAbs("x",Tx("t"),Mx("x")))(
        parseM "λx:t.x")
    end;
    "app" >:: begin fun () ->
      assert_equal (MApp(MAbs("x",Tx("t"),Mx("x")),MInt(1)))(
        parseM("(λx:t.x) 1"))
    end;
    "tapp" >:: begin fun () ->
      assert_equal (MTApp(Mx("x"),[TInt]))(parseM("x!int"))
    end;
    "record" >:: begin fun () ->
      assert_equal (MRecord ["x",MInt(1);"y",MInt(2)])(
        parseM("{x=1,y=2}"));
      assert_equal (MDot(MRecord ["x",MInt(1);"y",MInt(2)],
                        TRecord ["x",TInt;"y",TInt],"x"))(
        parseM("{x=1,y=2}:{x:int,y:int}#x"))
    end;
    "poly" >:: begin fun () ->
      assert_equal (MPoly(MInt(55),TInt))(
        parseM("Poly(55:int)"))
    end;
    "record2" >:: begin fun () ->
      assert_equal (MModify(MRecord ["x",MInt(1);"y",MInt(2)],
                           TRecord ["x",TInt;"y",TInt],"x",MInt(2)))(
        parseM("modify({x=1,y=2}:{x:int,y:int},x,2)"))
    end;
    "record3" >:: begin fun () ->
      assert_equal (MApp(MAbs("z",TInt,MRecord ["y",Mx("z")]),MInt(1)))(
        parseM("(λz:int.{y=z}) 1"))
    end;
    "record4" >:: begin fun () ->
      assert_equal (MModify(
        MApp(MAbs("z",TInt,MRecord ["x",MInt(1);"y",Mx("z")]),MInt(1)),
        TRecord ["x",TInt;"y",TInt],"x",MInt(2)))(
        parseM("modify(((λz:int.{x=1,y=z}) 1):{x:int,y:int},x,2)"))
    end;
    "variant" >:: begin fun () ->
      assert_equal (MVariant("eint",MInt(1),TVariant ["eint",TInt;"eadd",TRecord ["_1",TInt;"_2",TInt]]))(
        parseM("<eint=1>:<eint:int,eadd:{_1:int,_2:int}>"))
    end;
    "variant2" >:: begin fun () ->
      assert_equal (
        MCase(MVariant("eint",MInt(1),TVariant ["eint",TInt]),
          ["eint",MAbs("x",TInt,Mx("x"))])
        )(
          parseM("case<eint=1>:<eint:int>of<eint=λx:int.x>")
        )
    end;
    "variant3" >:: begin fun () ->
      assert_equal (
        MCase(MApp(MAbs("z",TInt,MVariant("eint",Mx("z"),TVariant ["eint",TInt])),MInt(1)),
          ["eint",MAbs("x",TInt,Mx("x"))])
      )(
        parseM("case (λz:int.<eint=z>:<eint:int>) 1 of<eint=λx:int.x>")
      )
    end;
    "variant4" >:: begin fun () ->
      assert_equal (
        MCase(MApp(MAbs("z",TInt,MVariant("eint",Mx("z"),TVariant ["eint",TInt; "b",TInt])),MInt(1)),
          ["eint",MAbs("x",TInt,Mx("x")); "b",MAbs("x",TInt,Mx("x"))])
      )(
        parseM("case (λz:int.<eint=z>:<eint:int,b:int>) 1 of<eint=λx:int.x,b=λx:int.x>")
      )
    end;
    "let" >:: begin fun () ->
      assert_equal (MLet("x",TInt,MPoly(MInt(1),TInt),Mx("x")))(
        parseM("let x:int=Poly(1:int) in x"))
    end;
    "let2" >:: begin fun () ->
      assert_equal (MLet("x",TAll("x0",U,TArr(Tx("x0"),Tx("x0"))),
        MPoly(MAbs("x",Tx("x0"),Mx("x")),TAll("x0",U,TArr(Tx("x0"),Tx("x0")))),MTApp(Mx("id"),[Tx("x1")])))(
        parseM "let x: ∀x0::U.x0->x0=Poly((λx:x0.x):∀x0::U.x0->x0) in id!x1")
    end;
    "let3" >:: begin fun () ->
      assert_equal
        (MLet("x",TAll("x0",U,TArr(Tx("x0"),Tx("x0"))),
          MPoly(MAbs("x",Tx("x0"),Mx("x")),TAll("x0",U,TArr(Tx("x0"),Tx("x0")))),
          MApp(MTApp(Mx("id"),[TInt]),MInt(1))))
        (parseM "let x: ∀x0::U.x0->x0=Poly((λx:x0.x):∀x0::U.x0->x0) in id!int 1")
    end;
  ]
