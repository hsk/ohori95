let run src =
  Printf.printf "%s\n" "============";
  let e = Mss_lexer.parseE(src) in
  Printf.printf "%s\n" (Mss.show e);
  (*
  Tmss.reset();
  let (k,s,m,t) = Tmss.wk(Map(),Map(),e) in
  let (k1,t1) = Tmss.cls(k,s,t) in
  let m_ = Tmss.mtsub(s,m) in
  Printf.printf "%s\n" (m_);
  Printf.printf "%s\n" ("k="+k+ " lk="+ics.lk(k));
  let c_ = ics.c(ics.lk(k),Map(),m_) in
  Printf.printf "%s\n" (c_);
  Printf.printf "%s\n" ("------------ eval "+c_);
  Printf.printf "%s\n" (ics.eval(c_)+":"+Tmss.tsub(s,t1));
  *)
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
