open OUnit

open Mss
open Mss_lexer

let test () =
  "parse E" >::: [
    "i" >:: begin fun () ->
      assert_equal(EInt(1))(parseE("1"));
      assert_equal(EInt(10))(parseE("10"));
      assert_equal(EInt(-10))(parseE("-10"));
    end;
    "cb" >:: begin fun () ->
      assert_equal(ETrue)(parseE("true"));
      assert_equal(EFalse)(parseE("false"));
    end;
    "x" >:: begin fun () ->
      assert_equal(Ex("x"))(parseE("x"));
    end;
    "λ" >:: begin fun () ->
      assert_equal(EAbs("x",Ex("x")))(parseE("λx.x"));
    end;
    "app" >:: begin fun () ->
      assert_equal(EApp(EAbs("x",Ex("x")),EInt(1)))(
        parseE("(λx.x) 1"));
      assert_equal(EApp(EApp(Ex("a"),Ex("b")),Ex("c")))
                  (parseE("a b c"));
    end;
    "record" >:: begin fun () ->
      assert_equal(ERecord["x",EInt(1);"y",EInt(2)])(
        parseE("{x=1,y=2}"));
      assert_equal(EDot(ERecord["x",EInt(1);"y",EInt(2)],"x"))(
        parseE("{x=1,y=2}#x"));
    end;
    "record2" >:: begin fun () ->
      assert_equal(EModify(ERecord["x",EInt(1);"y",EInt(2)],"x",EInt(2)))(
        parseE("modify({x=1,y=2},x,2)"));
    end;
    "variant" >:: begin fun () ->
      assert_equal(EVariant("eint",EInt(1)))(
        parseE("<eint=1>"));
    end;
    "variant2" >:: begin fun () ->
      assert_equal(
        ECase(EVariant("eint",EInt(1)),[
          "eint",EAbs("x",Ex("x"));
          "eadd",EAbs("x",EApp(EApp(Ex("add"),EDot(Ex("x"),"_1")),EDot(Ex("x"),"_2")))
        ])
      )(
        parseE("
        case <eint=1> of <
          eint=λx.x,
          eadd=λx.add x#_1 x#_2
        >
        ")
      );
    end;
    "let" >:: begin fun () ->
      assert_equal(ELet("x",EInt(1),Ex("x")))(
        parseE("let x=1 in x"));
    end;
    "let2" >:: begin fun () ->
      assert_equal(ELet("id",EAbs("x",Ex("x")),EApp(Ex("id"),EInt(1))))(
        parseE("let id= λx.x in id 1"));
    end;
  ]
