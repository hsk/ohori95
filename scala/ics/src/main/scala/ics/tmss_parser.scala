package ics
import util.parsing.combinator._

object tmss_parser extends RegexParsers {
  import tmss._
  val keywords = Set("true","false","case","of","modify","Poly","let","in")
  val tkeywords = Set("int","bool","idx")

  def ATOM  = ("""[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ {case x=>x})
  def INT   = ("""-?[0-9]+""".r               ^^ {case a     => a.toInt})
  def t     = ("""[a-zA-Z_][a-zA-Z0-9_]*""".r ^? {case a if !tkeywords.contains(a) => a})
  def b     = ("int"                          ^^ {case _ => TInt}).
            | ("bool"                         ^^ {case _=> TBool})
  def l     = (ATOM                           ^^ {case x=>x})
  def σ     : Parser[q]
            = (σ1 ~ "->" ~ σ                  ^^ {case a~_~b=>TArr(a,b)}).
            | (σ1                             ^^ {case t=>t})
  def σ1    = (b                              ^^ {case b=>b}).
            | (t                              ^^ {case a=>Tx(a)}).
            | ("{" ~> repsep(lσ,",") <~ "}"   ^^ {case r => TRecord(r)}).
            | ("<" ~> repsep(lσ,",") <~ ">"   ^^ {case r => TVariant(r)}).
            | ("∀" ~ t ~ "::" ~ k ~ "." ~ σ   ^^ {case _~t~_~k~_~σ => TAll(t,k,σ)}).
            | ("idx" ~>"(" ~>t ~("," ~>σ<~")")~("=>"~>σ)
                                              ^^ {case t~σ1~σ2 => TIdx(t,σ1,σ2)}).
            | ("("~> σ <~")")
  def lσ    = l ~ ":" ~ σ                     ^^ {case a~_~b=>(a,b)}
  def k     = ("U"                            ^^ {case _=>U}).
            | ("{{" ~> repsep(lσ,",") <~ "}}" ^^ {case r => KRecord(r)}).
            | ("<<" ~> repsep(lσ,",") <~ ">>" ^^ {case r => KVariant(r)})

  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})
  def i     = (INT                            ^^ {case i=>MInt(i)})
  def cb    = ("true"                         ^^ {case _=>MTrue}).
            | ("false"                        ^^ {case _=>MFalse}).
            | (i                              ^^ {case m=>m})

  def M     : Parser[m]
            = (rep1(M1)                       ^^ {case ms=>ms.reduceLeft{MApp}})
  def M1    = (M2 ~ rep(":" ~>σ ~ ("#" ~>l))  ^^ {case m~ls=>ls.foldLeft(m){case(m,(σ~l))=>MDot(m,σ,l)}})
  def M2    = (M3 ~ rep("!" ~>σ)              ^^ {case m~List()=>m case m~σs=>MTApp(m,σs)})
  def M3    = (x                              ^^ {case x=>Mx(x)}).
            | (cb                             ^^ {case m=>m}).
            | ("λ" ~ x ~ ":" ~ σ ~ "." ~ M    ^^ {case _~x~_~σ~_~m=>MAbs(x,σ,m)}).
            | ("{" ~> repsep(lM,",") <~ "}"   ^^ {case r => MRecord(r)}).
            | ("<" ~> lM ~ ">" ~ ":" ~ σ      ^^ {case (l,m)~_~_~σ => MVariant(l,m,σ)}).
            | ("case"~M~"of"~"<"~repsep(lM,",")~">"
                                              ^^ {case _~m~_~_~lMs~_=>MCase(m,lMs)}).
            | ("modify"~>"("~>M~":"~σ~","~l~","~M<~")"
                                              ^^ {case m~_~σ~_~l~_~m2=>MModify(m,σ,l,m2)}).
            | ("Poly"~>"("~> M~":"~σ <~")"    ^^ {case m~_~σ=>MPoly(m,σ)}).
            | ("let"~>x~":"~ σ~"="~M~"in"~M   ^^ {case x~_~σ~_~m~_~m2=>MLet(x,σ,m,m2)}).
            | ("("~M~")"                      ^^ {case _~m~_=>m})
  def lM    = l ~ "=" ~ M                     ^^ {case a~_~b=>(a,b)}

  def parsek(s:String):k = {
    parseAll(k, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
  def parseσ(s:String):q = {
    parseAll(σ, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
  def parseM(s:String):m = {
    parseAll(M, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
}
