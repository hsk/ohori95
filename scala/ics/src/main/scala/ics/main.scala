package ics

object main extends App {
  def run(src:String) {
    mss2.reset()
    val e:mss2.E = mss2parser.parseE(src)
    val (k,s,m,t) =mss2.wk(Map(),Map(),e)
    val (_,t1)=mss2.cls(k,Map(),t)
    val m_ = mss2.mtsub(s,m)
    val c_ = ics.c(ics.lk(k),Map(),m_)
    println(c_)
    println(ics.eval(c_))
  }
  run("1")
  run("{x=1,y=2}")
  run("(λa.a#x){x=1,y=2}")
  run("(λa.{k=a#y}){x=1,y=2}")
  //run("(λa.{k=a#x,j=a#y}){x=1,y=2}")
}
