open OUnit
open Utils
open Mss
open Tmss
open Ics
open Ics_lexer
let parseq = Tmss_lexer.parseq
let parsek = Tmss_lexer.parsek
let parseM = Tmss_lexer.parseM
(*
import tmss._

  def test(a:String,b:Boolean) = it(a) {assert(b)}
*)
let test_csub () =
  "csub" >::: [
    "cb" >:: begin fun () ->
      assert_equal(csub(M.singleton "x" (Cx "y"),parseC("1")))(parseC("1"));
      assert_equal(csub(M.singleton "x" (Cx "y"),parseC("true")))(parseC("true"));
      assert_equal(csub(M.singleton "x" (Cx "y"),parseC("false")))(parseC("false"));
    end;
    "x" >:: begin fun () ->
      assert_equal(csub(M.of_list ["x",Cx("y")],parseC("x")))(parseC("y"));
      assert_equal(csub(M.of_list ["x",Cx("y");"y",Cx("z")],parseC("x")))(parseC("z"));
      assert_equal(csub(M.of_list ["y",Cx("z");"x",Cx("y")],parseC("x")))(parseC("z"));
      assert_equal(csub(M.of_list ["x",Cx("y");"y",Cx("z")],parseC("x")))(parseC("z"));
      assert_equal(csub(M.of_list ["y",Cx("z");"x",Cx("y")],parseC("x")))(parseC("z"));
    end;
    "λ" >:: begin fun () ->
      assert_equal(csub(M.of_list ["x",Cx("y");"y",Cx("z")],parseC("λx.x")))(parseC("λx.x"));
      assert_equal(csub(M.of_list ["x",Cx("y");"y",Cx("z")],parseC("λa.x")))(parseC("λa.z"));
      assert_equal(csub(M.of_list ["y",Cx("z");"x",Cx("y")],parseC("λa.x")))(parseC("λa.z"));
    end;
  ]
let test_eval () =
  "eval" >::: [
    "λ" >:: begin fun () ->
      assert_equal(parseC("1"))(Ics.eval(parseC("(λx.x) 1")));
      assert_equal(parseC("10"))(Ics.eval(parseC("(λz.z) ((λx.x) 10)")));
    end;
    "record" >:: begin fun () ->
      assert_equal(parseC("10"))(Ics.eval(parseC("{10,20}[1]")));
      assert_equal(parseC("20"))(Ics.eval(parseC("{10,20}[2]")));
      assert_equal(parseC("11"))(Ics.eval(parseC("{(λx.x) 11,2}[1]")));
      assert_equal(parseC("22"))(Ics.eval(parseC("{(λx.x) 11,(λy.y) 22}[2]")));
    end;
    "record modify" >:: begin fun () ->
      assert_equal(parseC("{10,22}"))(
        Ics.eval(parseC("modify({11,22},1,10)")));
      assert_equal(parseC("{11,10}"))(
        Ics.eval(parseC("modify({11,22},2,10)")));
    end;
    "record app" >:: begin fun () ->
      assert_equal(parseC("{10}"))(
        Ics.eval(parseC("(λz.{z}) 10")));
    end;
    "record4" >:: begin fun () ->
      assert_equal(parseC("{11,10}"))(
        Ics.eval(parseC("(λz.{11,z}) ((λx.x) 10)")));
      assert_equal(parseC("{22,10}"))(
        Ics.eval(parseC("modify((λz.{11,z}) 10,1,22)")));
    end;
    "variant" >:: begin fun () ->
      assert_equal(parseC("<1=1>"))(Ics.eval(parseC("<1=1>")));
    end;
    "variant2" >:: begin fun () ->
      assert_equal(parseC("1"))(
        Ics.eval(parseC("switch (λz.<1=z>) 1 of λx.x,λx.add x[1] x[2]")));
    end;
    "variant3" >:: begin fun () ->
      assert_equal(parseC("{10,1}"))(
        Ics.eval(parseC("switch (λz.<2={z,10}>) 1 of λx.x,λx.{x[2],x[1]}")));
    end;
  ]
let test_kinding () =
  "kinding" >::: [
    (*
    test(kinding_int):- [] ⊢ int:k,k=u,!.
    test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[x:int],!.
    test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[x:int,y:int],!.
    % test(kinding_t):- [a:[x:int,y:int]] ⊢ a:k,k=[y:int]. todo
    % test(kinding_record):- [] ⊢ [x:int,y:int]:k,k=[x:int],!.
    test(kinding_record):- [] ⊢ [x:int,y:int]:k,k=[x:int,y:int],!.
    test(kinding_variant_t):- [a:{[x:int,y:int]}] ⊢ a:k,k={[x:int]},!.
    test(kinding_variant_t):- [a:{[x:int,y:int]}] ⊢ a:k,k={[x:int,y:int]},!.
    % test(kinding_variant):- [] ⊢ {[x:int,y:int]}:k,k={[x:int]},!.
    test(kinding_variant):- [] ⊢ {[x:int,y:int]}:k,k={[x:int,y:int]},!.
    *)
  ]
let test_index_judgment () =
  "index_judgment" >::: [
    (*
    test('IVAR I') :- [k:idx(x,int)] ⊢ k : idx(x,int),!.
    test('IVAR i record') :- [] ⊢ 1 : idx(k,[k:int,j:int]),!.
    test('IVAR i record') :- [] ⊢ 2 : idx(j,[k:int,j:int]),!.
    test('IVAR i variant') :- [] ⊢ 1 : idx(k,{[k:int,j:int]}),!.
    test('IVAR i variant') :- [] ⊢ 2 : idx(j,{[k:int,j:int]}),!.
    *)
  ]

let test_rep () =
  "*" >::: [
    "getT" >:: begin fun () ->
      assert_equal(sortq(parseq("∀t2::{{b:int,a:bool}}.∀t3::{{a:t2}}.t2->t3")))
                  ((["t2",parsek("{{a:bool,b:int}}");"t3",parsek("{{a:t2}}")],parseq("t2->t3")))
    end;
    "rep" >:: begin fun () ->
      assert_equal(
        addIdx(parseq("∀t2::{{b:int,a:bool}}.∀t3::{{a:t2}}.t2->t3")))
              (parseq("∀t2::{{a:bool,b:int}}.∀t3::{{a:t2}}.idx(a,t2)=>idx(b,t2)=>idx(a,t3)=>t2->t3"))
    end;
    "rep2" >:: begin fun () ->
      assert_equal(addIdx(parseq("∀x2::{{a:x1}}.x2->x1")))
                         (parseq("∀x2::{{a:x1}}.idx(a,x2)=>x2->x1"))
    end;
    "rep3" >:: begin fun () ->
      assert_equal(addIdx(parseq("∀x1::U.∀x2::{{a:x1}}.x2->x1")))(
                                     parseq("∀x1::U.∀x2::{{a:x1}}.idx(a,x2)=>x2->x1"))
    end;
    "rep4" >:: begin fun () ->
      assert_equal(addIdx(parseq("∀x2::{{a:x1}}.x2->x1")))(
                                     parseq("∀x2::{{a:x1}}.idx(a,x2)=>x2->x1"))
    end;
    "rep5" >:: begin fun () ->
      assert_equal(addIdx(parseq("∀x1::U.∀x2::{{a:x1}}.x2->x1")))(
                                     parseq("∀x1::U.∀x2::{{a:x1}}.idx(a,x2)=>x2->x1"))
    end;
  ]
let test_compile () =
  let test((e:x), (m:x), (t:x), (cx:x)) =
    assert_equal(parseC(cx))(c([],M.empty,parseM(m)))
  in
  let tesk((e:x), (m:x), (t:x), (eK:(q * k) list), (cx:x)) =
    assert_equal(parseC(cx))(c(lk(Q.of_list eK),M.empty,parseM(m)))
  in
  "compile" >::: [
    "int"      >:: begin fun () -> test("10",   "10"   ,"int" ,"10") end;
    "true"     >:: begin fun () -> test("true", "true" ,"bool","true") end;
    "false"    >:: begin fun () -> test("false","false","bool","false") end;
    "λ"        >:: begin fun () -> test("λ(x,x)",
                          "λx:x0.x", "∀x0::U.x0->x0",
                          "λx.x") end;
    "app"      >:: begin fun () ->
                     test("(λx.x) 1",
                          "(λx:int.x) 1","int",
                          "(λx.x) 1") end;
    "record"   >:: begin fun () ->
                     test("{x=10,y=20}",
                          "{x=10,y=20}","{x:int,y:int}",
                          "{10,20}") end;
    "record2"  >:: begin fun () ->
                     test("{x=10,y=20}#x",
                          "{x=10,y=20}:{x:int,y:int}#x","int",
                          "{10,20}[1]") end;
    "record3"  >:: begin fun () ->
                     test("{x=10,y=20}#y",
                          "{x=10,y=20}:{x:int,y:int}#y","int",
                          "{10,20}[2]") end;
    "record4"  >:: begin fun () ->
                     test("{x=(λx.x) 1,y=2}#x",
                          "{x=(λx:int.x) 1,y=2}:{x:int,y:int}#x","int",
                          "{(λx.x) 1,2}[1]") end;
    "record5"  >:: begin fun () ->
                     test("modify({x=10,y=20},x,30)",
                          "modify({x=10,y=20}:{x:int,y:int},x,30)","{x:int,y:int}",
                          "modify({10,20},1,30)") end;
    "record6"  >:: begin fun () ->
                     test("(λz.{y=z}) 10",
                          "(λz:int.{y=z}) 10","{y:int}",
                          "(λz.{z}) 10") end;
    "record7"  >:: begin fun () -> resetn(2);
                     tesk("λz.z#a",
                          "λz:x2.z:x2#a","∀x1::U.∀x2::{{a:x1}}.x2->x1",
                          [Tx("x1"),U;Tx("x2"),parsek("{{a:x1}}")],
                          "λz.z[x2]") end;
    "record8"  >:: begin fun () ->
                     test("modify((λz.{x=1,y=z}) 10,x,2)",
                          "modify(((λz:int.{x=1,y=z}) 10):{x:int,y:int},x,2)","{x:int,y:int}",
                          "modify((λz.{1,z}) 10,1,2)") end;
    "variant"  >:: begin fun () -> resetn(3);
                     tesk("<eint=1>",
                          "(<eint=1>:x0)","∀(x0,<eint:int>,x0)",
                          [Tx("x0"),parsek("<<eint:int>>")],
                          "<x3=1>") end;
    "variant2" >:: begin fun () ->
                     test("case<eint=1>of<eint=λx.x>",
                          "case<eint=1>:<eint:int>of<eint=λx:int.x>","int",
                          "switch <1=1> of λx.x") end;
    "variant3" >:: begin fun () ->
                     test("case(λz.<eint=z>) 1 of<eint=λx.x>",
                          "case(λz:int.<eint=z>:<eint:int>) 1 of<eint=λx:int.x>","int",
                          "switch(λz.<1=z>) 1 of λx.x") end;
    "variant4" >:: begin fun () ->
                     test("case(λz.<eint=z>) 1 of<eint=λx.x,b=λx.x>",
                          "case(λz:int.<eint=z>:<eint:int,b:int>) 1 of<eint=λx:int.x,b=λx:int.x>","int",
                          "switch(λz.<1=z>) 1 of λx.x,λx.x") end;
    "let"      >:: begin fun () ->
                     test("let x=1 in x",
                          "let x:int=Poly(1:int) in x","int",
                          "let x=1 in x") end;
    "let2" >:: begin fun () ->
      tesk("let id=λx.x in id",
           "let id:∀x0::U.x0->x0
                  =Poly((λx:x0.x) : ∀x0::U.x0->x0) in id!x1", "∀x1::U.x1->x1",
            [Tx("x1"),U],
           "let id=λx.x in id") end;
    "let3" >:: begin fun () ->
      test("let id=λx.x in id 1",
           "let id:∀x0::U.x0->x0
                  =Poly((λx:x0.x) : ∀x0::U.x0->x0) in (id!int) 1","int",
           "let id=λx.x in id 1") end;
    "let4" >:: begin fun () ->
      test("let id=λx.λy.x in id 1 2",
           "let id: ∀x1::U.∀x0::U.x0->x1->x0
                  = Poly((λx:x0.λy:x1.x) : ∀x1::U.∀x0::U.x0->x1->x0) in
                  (id!int!int) 1 2","int",
           "let id=λx.λy.x in id 1 2") end;
    "let_poly" >:: begin fun () ->
      resetn(5);
      tesk("let id=λx.x#a in id",
           "let id: ∀x1::U.∀x2::{{a:x1}}.x2->x1
                    =Poly((λx:x2.x:x2#a): ∀x1::U.∀x2::{{a:x1}}.x2->x1) in
                    id!x3!x4", "∀x3::U.∀x4::{{a:x3}}.x4->x3",
            [Tx("x3"),U;Tx("x4"),parsek("{{a:x3}}")],
           "let id=λx6.λx.x[x6] in id x5") end;
    "let_poly2" >:: begin fun () ->
      resetn(3);
      test("let id=λx.x#a in id {a=10,b=20}",
           "let id: ∀x2::{{a:x1}}.∀x1::U.x2->x1
                  =Poly((λx:x2.x:x2#a): ∀x2::{{a:x1}}.∀x1::U.x2->x1) in
                  id!{a:int,b:int}!int {a=10,b=20}","int",
           "let id=λx3.λx.x[x3] in id 1 {10,20}") end;
  ]
