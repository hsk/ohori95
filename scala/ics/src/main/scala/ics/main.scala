package ics

object main extends App {
  def run(src:String) {
    println("============")
    tmss.reset()
    val e = mss_parser.parseE(src)
    val (k,s,m,t) = tmss.wk(Map(),Map(),e)
    val (k1,t1) = tmss.cls(k,s,t)
    val m_ = tmss.mtsub(s,m)
    println(e)
    println(m_)
    println("k="+k+ " lk="+ics.lk(k))
    val c_ = ics.c(ics.lk(k),Map(),m_)
    println(c_)
    println("------------ eval "+c_)
    println(ics.eval(c_))
  }
  run("1")
  run("{x=1,y=2}")
  run("(λa.a#x){x=1,y=2}")
  run("(λa.{k=a#y}){x=1,y=2}")
  run("(λa.{k=a#x,j=a#y}){x=1,y=2}")
  run("let f= λa.{k=a#x,j=a#y} in f {x=1,y=2,z=5}")
  run("let f= λa.a#x in f {x=1}")
  run("let f= λa.λb.modify(a,x,b) in f {x=1} 2")
  run("let f= λa.λb.modify(a,x,b) in f {z=5,x=1} 2")
  run("{z=(λy.λx.{a=x,b=y}) 1 2}")
  run("let f= λa.λb.modify(a,x,b) in {aa=f {z=5,x=1} 2,bb=f{x=1,y=5}2}")
  run("let f= λa.λb.λc.modify(modify(a,x,b),z,c) in {aa=f {z=5,x=1} 10 20,bb=f{z=0,x=1,y=5}10 20}")
  run("<x={a=1,b=2}>")
  run("case <x={a=1}> of <x=λy.y#a>") // todo add test
  run("(λv.case v of <x=λy.y#a>) <x={a=1}>") // todo add test
  run("let f=λv.case v of <x=λy.y#c> in f <x={b=2,c=1}>") // todo add test
}
