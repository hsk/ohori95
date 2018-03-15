open OUnit
open Ics
open Ics_lexer
let test_parseC () =
  "parse C" >::: [
    "i" >:: begin fun () ->
      assert_equal(CInt(1))(parseC("1"));
      assert_equal(CInt(10))(parseC("10"));
      assert_equal(CInt(-10))(parseC("-10"));
    end;
    "cb" >:: begin fun () ->
      assert_equal(CTrue)(parseC("true"));
      assert_equal(CFalse)(parseC("false"));
    end;
    "x" >:: begin fun () ->
      assert_equal(Cx("x"))(parseC("x"));
    end;
    "λ" >:: begin fun () ->
      assert_equal(CAbs("x",Cx("x")))(parseC("λx.x"));
    end;
    "app" >:: begin fun () ->
      assert_equal(CApp(CAbs("x",Cx("x")),CInt(1)))(
        parseC("(λx.x) 1"))
    end;
    "record" >:: begin fun () ->
      assert_equal(CRecord([CInt(1);CInt(2)]))(
        parseC("{1,2}"));
      assert_equal(CDot(CRecord([CInt(1);CInt(2)]),CInt(1)))(
        parseC("{1,2}[1]"));
    end;
    "record2" >:: begin fun () ->
      assert_equal(CModify(CRecord([CInt(1);CInt(2)]),CInt(1),CInt(2)))(
        parseC("modify({1,2},1,2)"));
    end;
    "variant" >:: begin fun () ->
      assert_equal(CVariant(CInt(1),CInt(1)))(
        parseC("<1=1>"));
    end;
    "variant2" >:: begin fun () ->
      assert_equal(
        CSwitch(CVariant(CInt(1),CInt(1)),
          [
            CAbs("x",Cx("x"));
            CAbs("x",CApp(CApp(Cx("add"),CDot(Cx("x"),CInt(1))),CDot(Cx("x"),CInt(2))))]
          )
        )(
          parseC("
          switch <1=1> of
            λx.x,
            λx.add (x[1]) (x[2])
          ")
        )
    end;
    "let" >:: begin fun () ->
      assert_equal(CLet("x",CInt(1),Cx("x")))(
        parseC("let x=1 in x"))
    end;
    "let2" >:: begin fun () ->
      assert_equal(CLet("id",CAbs("x",Cx("x")),CApp(Cx("id"),CInt(1))))(
        parseC("let id= λx.x in id 1"))
    end;
  ]
