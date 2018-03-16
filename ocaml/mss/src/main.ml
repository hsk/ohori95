open Mss_lexer
open Tmss_lexer
open Tmss
open Utils

let run src =
  Printf.printf "%s\n" "============";
  let e = parseE(src) in
  Printf.printf "%s\n" (Mss.show e);
  Tmss.reset();
  let (k,s,m,t) = Tmss.wk(Q.empty,M.empty,e) in
  let (k1,t1) = Tmss.cls(k,s,t) in
  let m_ = Tmss.mtsub(s,m) in
  Printf.printf "%s\n" (show m_);
  Printf.printf "k=%s lk=%s\n" (show_eK k) (Ics.show_eL (Ics.lk k));
  let c_ = Ics.c(Ics.lk(k),M.empty,m_) in
  Printf.printf "%s\n" (Ics.show c_);
  Printf.printf "------------ eval %s\n" (Ics.show c_);
  Printf.printf "%s : %s\n" (Ics.show (Ics.eval(c_))) (show_q (Tmss.tsub(s,t1)));
  ()
let () =
  run "1";
  run "{x=1}";
  run "{x=1,y=2}";
  run "(λa.a#x){x=1,y=2}";
  run "(λa.{k=a#y}){x=1,y=2}";
  run "(λa.{k=a#x,j=a#y}){x=1,y=2}";
  run "let f= λa.{k=a#x,j=a#y} in f {x=1,y=2,z=5}";
  run "let f= λa.a#x in f {x=1}";
  run "let f= λa.λb.modify(a,x,b) in f {x=1} 2";
  run "let f= λa.λb.modify(a,x,b) in f {z=5,x=1} 2";
  run "{z=(λy.λx.{a=x,b=y}) 1 2}";
  run "let f= λa.λb.modify(a,x,b) in {aa=f {z=5,x=1} 2,bb=f{x=1,y=5}2}";
  run "let f= λa.λb.λc.modify(modify(a,x,b),z,c) in {aa=f {z=5,x=1} 10 20,bb=f{z=0,x=1,y=5}10 20}";
  run "<x={a=1,b=2}>";
  run "case <x={a=1}> of <x=λy.y#a>";
  run "(λv.case v of <x=λy.y#a>) <x={a=1}>";
  run "let f=λv.case v of <x=λy.y#c> in f <x={b=2,c=1}>";
  run "let f=λv.case v of <x=λy.y#c> in f";
  ()
