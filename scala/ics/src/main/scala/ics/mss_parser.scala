package ics
import util.parsing.combinator._

object mss_parser extends RegexParsers {
  import mss._
  val keywords = Set("true","false","case","of","modify","Poly","let","in")
  val tkeywords = Set("int","bool","idx")

  def ATOM  = ("""[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ {case x=>x})
  def INT   = ("""-?[0-9]+""".r               ^^ {case a     => a.toInt})
  def t     = ("""[a-zA-Z_][a-zA-Z0-9_]*""".r ^? {case a if !tkeywords.contains(a) => a})
  def b     = ("int"                          ^^ {case _ => TInt}).
            | ("bool"                         ^^ {case _=> TBool})
  def l     = (ATOM                           ^^ {case x=>x})
  def σ     : Parser[σ]
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
            | ("{{" ~> repsep(lσ,",") <~ "}}" ^^ {case r => krecord(r)}).
            | ("<<" ~> repsep(lσ,",") <~ ">>" ^^ {case r => kvariant(r)})

  def i     = (INT                            ^^ {case i=>EInt(i)})
  def cb    = ("true"                         ^^ {case _=>ETrue}).
            | ("false"                        ^^ {case _=>EFalse}).
            | (i                              ^^ {case i=>i})
  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})

  def e     : Parser[E]
            = (rep1(e1)                       ^^ {case es=>es.reduceLeft{EApp}})
  def e1    = (e2 ~ rep("#" ~> l)             ^^ {case e~ls=>ls.foldLeft(e){EDot}})
  def e2    = (x                              ^^ {case x=>Ex(x)}).
            | (cb).
            | ("λ" ~ x ~ "." ~ e              ^^ {case _~x~_~e=>EAbs(x,e)}).
            | ("{" ~> repsep(le,",") <~ "}"   ^^ {case r => ERecord(r)}).
            | ("<" ~> le <~ ">"               ^^ {case (l,e) => EVariant(l,e)}).
            | ("case"~e~"of"~"<"~repsep(le,",")~">"
                                              ^^ {case _~e~_~_~les~_=>ECase(e,les)}).
            | ("modify"~>"("~>e~","~l~","~e<~")"
                                              ^^ {case e~_~l~_~e2=>EModify(e,l,e2)}).
            | ("let"~>x~"="~e~"in"~e          ^^ {case x~_~e~_~e2=>ELet(x,e,e2)}).
            | ("("~>e<~")"                    ^^ {case e=>e})
  def le    = l ~ "=" ~ e                     ^^ {case a~_~b=>(a,b)}

  def mi    = (INT                            ^^ {case i=>MInt(i)})
  def mcb   = ("true"                         ^^ {case _=>MTrue}).
            | ("false"                        ^^ {case _=>MFalse}).
            | (mi                             ^^ {case m=>m})

  def M     : Parser[M]
            = (rep1(M1)                       ^^ {case ms=>ms.reduceLeft{MApp}})
  def M1    = (M2 ~ rep(":" ~>σ ~ ("#" ~>l))  ^^ {case m~ls=>ls.foldLeft(m){case(m,(σ~l))=>MDot(m,σ,l)}})
  def M2    = (M3 ~ rep("!" ~>σ)              ^^ {case m~σs=>σs.foldLeft(m){MTApp}})
  def M3    = (x                              ^^ {case x=>Mx(x)}).
            | (mcb                            ^^ {case m=>m}).
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
  def parseE(s:String):E = {
    parseAll(e, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
  def parseM(s:String):M = {
    parseAll(M, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
  def parseσ(s:String):σ = {
    parseAll(σ, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
}
