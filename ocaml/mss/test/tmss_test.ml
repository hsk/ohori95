open OUnit
open Mss
open Tmss
open Utils
let parseE = Mss_lexer.parseE
let parsek = Tmss_lexer.parsek
let parseq = Tmss_lexer.parseq
let parseM = Tmss_lexer.parseM

let test_eftv () =
  "eftv" >::: [
    "a" >:: begin fun () ->
      assert_equal(eftv(Q.of_list[Tx "t1",U;Tx "t2",parsek "{{l:t1}}"],parseq "t1")) ["t1"];
      assert_equal(eftv(Q.of_list[Tx "t1",U;Tx "t2",parsek "{{l:t1}}"],parseq "t2")) ["t2";"t1"];
    end;
  ]

let test_cls () =
  "cls" >::: [
    "a" >:: begin fun () ->
    (*
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t1,R),!,R=([t2:[l:t1]],∀(t1,u,t1)).
    test(a) :- cls([t1 : u, t2 : [l:t1]],[],t2,R),!,R=([],∀(t1,u,∀(t2,[l:t1],t2))).
    *)
      ()
    end;
  ]
let test_typing () =
  let test(e,em,t_) =
    reset();
    let (k,s,m,t) = wk(Q.empty,M.empty,parseE(e)) in
    (*println("test k="+k+" t="+t)*)
    let (_,t1) = cls(k,M.empty,t) in
    (*println("test t1="+t1)*)
    let m_ = mtsub(s,m) in
    Printf.printf "m=%s t1=%s\n" (Tmss.show m_) (show_q t1);
    assert_equal (parseM em) m_;
    assert_equal (parseq t_) t1;
  in
  let tesk(e,em,eq_,eK_) =
    reset();
    let (k,s,m,t) = wk(Q.empty,M.empty,parseE e) in
    let (_,t1) = cls(k,M.empty,t) in
    let m_ = mtsub(s,m) in
    (*Printf.printf "m=%s t1=%s\nek=%s\n" (Tmss.show m) (show_q t1) (show_eK k);*)
    assert_equal (parseM em) m_;
    assert_equal (parseq eq_) t1;
    assert_equal (Q.of_list eK_) k;
  in
  "typing" >::: [
    "int"  >:: begin fun () -> test("10",   "10",   "int") end;
    "true" >:: begin fun () -> test("true", "true", "bool") end;
    "false">:: begin fun () -> test("false","false","bool") end;
    "λ"    >:: begin fun () -> test("λx.x", "λx:x0.x", "∀x0::U.x0->x0") end;
    "app"  >:: begin fun () -> test(
      "(λx.x) 1",
      "(λx:int.x) 1", "int") end;
    "record" >:: begin fun () -> test(
      "{x=1,y=2}",
      "{x=1,y=2}","{x:int,y:int}") end;
    "record2" >:: begin fun () -> test(
      "{x=1,y=2}#x",
      "{x=1,y=2}:{x:int,y:int}#x","int") end;
    "record3" >:: begin fun () -> test(
      "{x=1,y=2}#y",
      "{x=1,y=2}:{x:int,y:int}#y","int") end;
    "record4" >:: begin fun () -> test(
      "{x=(λx.x) 1,y=2}#x",
      "{x=(λx:int.x) 1,y=2}:{x:int,y:int}#x","int") end;
    "record5" >:: begin fun () -> test(
      "modify({x=1,y=2},x,2)",
      "modify({x=1,y=2}:{x:int,y:int},x,2)","{x:int,y:int}") end;
    "record6" >:: begin fun () -> test(
      "(λz.{y=z}) 10",
      "(λz:int.{y=z}) 10","{y:int}") end;
    "record7" >:: begin fun () -> tesk(
      "λz.z#a",
      "λz:x2.z:x2#a",
      "∀x2::{{a:x1}}.∀x1::U.x2->x1",
      [Tx("x1"),U;Tx("x2"),parsek("{{a:x1}}")]) end;
    "record8" >:: begin fun () -> test(
      "modify((λz.{x=1,y=z}) 10,x,2)",
      "modify(((λz:int.{x=1,y=z}) 10):{x:int,y:int},x,2)",
      "{x:int,y:int}") end;
    "record9" >:: begin fun () -> test(
      "(λa.{k=a#x,j=a#y}){x=1,y=2}",
      "(λa:{x:int,y:int}.{k=a:{x:int,y:int}#x,j=a:{x:int,y:int}#y}){x=1,y=2}",
      "{k:int,j:int}" ) end;
    "variant" >:: begin fun () -> tesk("<eint=1>",
      "<eint=1>:x0",
      "∀x0::<<eint:int>>.x0",
      [Tx("x0"), parsek("<<eint:int>>")]) end;
    "variant2" >:: begin fun () -> test(
      "case <eint=1> of <eint=λx.x>",
      "case <eint=1>:<eint:int> of <eint=λx:int.x>",
      "int") end;
    "variant3" >:: begin fun () -> test(
      "case (λz.<eint=z>) 1 of <eint=λx.x>",
      "case (λz:int.<eint=z>:<eint:int>) 1 of <eint=λx:int.x>",
      "int") end;
    "variant4" >:: begin fun () -> test(
      "case (λz.<eint=z>) 1 of <eint=λx.x,b=λx.x>",
      "case (λz:int.<eint=z>:<eint:int,b:int>) 1 of <eint=λx:int.x,b=λx:int.x>",
      "int") end;
    "variant5" >:: begin fun () -> test(
      "case <x={a=1}> of <x=λy.y#a>",
      "case <x={a=1}>:<x:{a:int}> of <x=λy:{a:int}.y:{a:int}#a>",
      "int") end;
    "let" >:: begin fun () -> test(
      "let x=1 in x",
      "let x:int=Poly(1:int) in x",
      "int") end;
    "let2" >:: begin fun () -> tesk(
      "let id=λx.x in id",
      "let id: ∀x0::U.x0->x0=Poly((λx:x0.x) : ∀x0::U.x0->x0) in id!x1",
      "∀x1::U.x1->x1",
      [Tx("x1"),U]) end;
    "let3" >:: begin fun () -> test(
      "let id=λx.x in id 1",
      "let id:∀x0::U.x0->x0=Poly((λx:x0.x) : ∀x0::U.x0->x0) in (id!int) 1",
      "int") end;
    "let4" >:: begin fun () -> test(
      "let id=λx.λy.x in id 1 2",
      "let id: ∀x1::U.∀x0::U.x0->x1->x0
             =Poly((λx:x0.λy:x1.x) : ∀x1::U.∀x0::U.x0->x1->x0)
       in (id!int!int) 1 2",
      "int") end;
    "let_poly" >:: begin fun () -> tesk(
      "let id = λx.x#a in id",
      "let id: ∀x2::{{a:x1}}.∀x1::U.x2->x1
         = Poly((λx:x2.x:x2#a) : ∀x2::{{a:x1}}.∀x1::U.x2->x1)
                       in id!x3!x4",
      "∀x4::U.∀x3::{{a:x4}}.x3->x4",
      [Tx("x3"),parsek("{{a:x4}}");Tx("x4"),U;]) end;
    "let_poly2" >:: begin fun () -> test(
      "let id=λx.x#a in id {a=10,b=20}",
      "let id: ∀x2::{{a:x1}}.∀x1::U.x2->x1
               = Poly((λx:x2.x:x2#a) : ∀x2::{{a:x1}}.∀x1::U.x2->x1)
                     in (id!{a:int,b:int}!int) {a=10,b=20}",
      "int") end;
  ]
