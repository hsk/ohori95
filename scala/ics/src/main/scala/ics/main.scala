package ics

object main extends App {
  def run(src:String) {
    mss2.reset()
    val e = mss2parser.parseE(src)
    val (k,s,m,t) = mss2.wk(Map(),Map(),e)
    val (_,t1) = mss2.cls(k,Map(),t)
    val m_ = mss2.mtsub(s,m)
    val c_ = ics.c(ics.lk(k),Map(),m_)
    println(m_)
    println(c_)
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
}