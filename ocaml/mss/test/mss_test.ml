open OUnit
open Mss
open Mss_lexer
open Utils

let esub () =
  "esub" >::: [
    "cb" >:: begin fun () ->
      assert_equal (esub (M.singleton "x" (Ex "y")) (parseE "1")) (parseE "1");
      assert_equal (esub (M.singleton "x" (Ex "y")) (parseE "true")) (parseE "true");
      assert_equal (esub (M.singleton "x" (Ex "y")) (parseE "false")) (parseE "false");
    end;
    "x" >:: begin fun () ->
      assert_equal (esub (M.of_list ["x",Ex "y"]) (parseE "x")) (parseE "y");
      assert_equal (esub (M.of_list ["x",Ex "y";"y",Ex "z"]) (parseE "x")) (parseE "z");
      assert_equal (esub (M.of_list ["y",Ex "z";"x",Ex "y"]) (parseE "x")) (parseE "z");
      assert_equal (esub (M.of_list ["x",Ex "y";"y",Ex "z"]) (parseE "x")) (parseE "z");
      assert_equal (esub (M.of_list ["y",Ex "z";"x",Ex "y"]) (parseE "x")) (parseE "z");
    end;
    "λ" >:: begin fun () ->
      assert_equal (esub (M.of_list ["x",Ex "y";"y",Ex "z"]) (parseE "λx.x")) (parseE "λx.x");
      assert_equal (esub (M.of_list ["x",Ex "y";"y",Ex "z"]) (parseE "λa.x")) (parseE "λa.z");
      assert_equal (esub (M.of_list ["y",Ex "z";"x",Ex "y"]) (parseE "λa.x")) (parseE "λa.z");
    end;
    (*
    todo:
    test(app) :- m(λ(x:t,x)$1).
    test(kapp) :- m(λ(x::u,x)$int).
    test(record) :- m([x=1,y=2]).
    test(record) :- m([x=1,y=2]#x).
    test(record) :- m(modify([x=1,y=2],x,2)).
    test(variant) :- m({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]}).
    test(variant) :- m(case({[eint=1]}:{[eint:int,eadd:['1':int,'2':int]]},{[eint=λ(x:int,x),eadd=λ(x:int,add$x#'1'$x#'2')]})),!.
    *)
  ]
let eval () =
  "eval">::: [
    "λ" >:: begin fun () ->
      assert_equal(parseE("1"))(eval(parseE("(λx.x) 1")));
      assert_equal(parseE("10"))(eval(parseE("(λz.z) ((λx.x) 10)")));
    end;
    "record" >:: begin fun () ->
      assert_equal(parseE("1"))(eval(parseE("{x=1,y=2}#x")));
      assert_equal(parseE("2"))(eval(parseE("{x=1,y=2}#y")));
      assert_equal(parseE("1"))(eval(parseE("{x=(λx.x) 1,y=2}#x")));
    end;
    "record2" >:: begin fun () ->
      assert_equal(parseE("{x=2,y=2}"))(
        eval(parseE("modify({x=1,y=2},x,2)")));
    end;
    "record3" >:: begin fun () ->
      assert_equal(parseE("{y=10}"))(
        eval(parseE("(λz.{y=z}) 10")));
    end;
    "record4" >:: begin fun () ->
      assert_equal(parseE("{x=1,y=10}"))(
        eval(parseE("(λz.{x=1,y=z}) ((λx.x) 10)")));
      assert_equal(parseE("{x=2,y=10}"))(
        eval(parseE("modify((λz.{x=1,y=z}) 10,x,2)")));
    end;
    "variant" >:: begin fun () ->
      assert_equal(parseE("<eint=1>"))(eval(parseE("<eint=1>")));
    end;
    "variant2" >:: begin fun () ->
      assert_equal(parseE("1"))(
        eval(parseE("case (λz.<eint=z>) 1 of<eint=λx.x,eadd=λx.add x#_1 x#_2>")));
    end;
  ]
