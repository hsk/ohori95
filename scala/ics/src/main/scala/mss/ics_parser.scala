package mss
import util.parsing.combinator._

object ics_parser extends RegexParsers {
  import ics._
  val keywords = Set("true","false","switch","of","modify","Poly","let","in")

  def ATOM= ("""[a-zA-Z_][a-zA-Z0-9_]*""".r    ^^ {case x=>x})
  def INT = ("""-?[0-9]+""".r                  ^^ {case a=>a.toInt})
  def x   = (ATOM                              ^? {case x if(!keywords.contains(x))=>x})
  def i   = (INT                               ^^ {case i=>CInt(i)})
  def cb  = ("true"                            ^^ {case _=>CTrue}).
          | ("false"                           ^^ {case _=>CFalse}).
          | (i                                 ^^ {case i=>i})
  def Ï   = (i                                 ^^ {case i=>i}).
          | (x                                 ^^ {case x=>Cx(x)})

  def c   : Parser[c]
          = (rep1(c1)                          ^^ {case cs=>cs.reduceLeft{CApp}})
  def c1  = (c2 ~ rep("["~> Ï <~"]")           ^^ {case c~ls=>ls.foldLeft(c){CDot}})
  def c2  = (x                                 ^^ {Cx(_)}).
          | (cb).
          | ("λ" ~ x ~ "." ~ c                 ^^ {case _~x~_~c=>CAbs(x,c)}).
          | ("{" ~> repsep(c,",") <~ "}"       ^^ {case r => CRecord(r)}).
          | ("<" ~> Ï ~ "=" ~ c <~ ">"         ^^ {case (l~_~c) => CVariant(l,c)}).
          | ("switch"~c~"of"~repsep(c,",")     ^^ {case _~c~_~cs=>CSwitch(c,cs)}).
          | ("modify"~>"("~>c~","~Ï~","~c<~")" ^^ {case c~_~i~_~c2=>CModify(c,i,c2)}).
          | ("let"~>x~"="~c~"in"~c             ^^ {case x~_~c~_~c2=>CLet(x,c,c2)}).
          | ("("~>c<~")"                       ^^ {case c=>c})

  def parseC(s:String):c = {
    parseAll(c, s) match {
      case Success(d, r) => d
      case e => throw new Exception(e.toString)
    }
  }
}
