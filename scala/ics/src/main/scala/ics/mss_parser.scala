package ics
import util.parsing.combinator._

object mss_parser extends RegexParsers {
  import mss._
  val keywords = Set("true","false","case","of","modify","Poly","let","in")

  def ATOM  = ("""[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ {case x=>x})
  def INT   = ("""-?[0-9]+""".r               ^^ {case a     => a.toInt})
  def l     = (ATOM                           ^^ {case x=>x})

  def i     = (INT                            ^^ {case i=>EInt(i)})
  def cb    = ("true"                         ^^ {case _=>ETrue}).
            | ("false"                        ^^ {case _=>EFalse}).
            | (i                              ^^ {case i=>i})
  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})

  def e     : Parser[e]
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

  def parseE(s:String):e = {
    parseAll(e, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
}
