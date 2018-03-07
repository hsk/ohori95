package ics
import util.parsing.combinator._

object ics_parser extends RegexParsers {
  import mss2._
  import ics._
  val keywords = Set("true","false","switch","of","modify","Poly","let","in")
  val tkeywords = Set("int","bool","idx")
  def ATOM  = """[a-zA-Z_][a-zA-Z0-9_]*""".r
  def INT   = """-?[0-9]+""".r                ^^ { case a     => a.toInt }
  def t     = """[a-zA-Z_][a-zA-Z0-9_]*""".r  ^? { case a if !tkeywords.contains(a) => a }
  def b     = ("int"                          ^^ {case _ => tint}).
            | ("bool"                         ^^ {case _=> tbool})
  def l     = ATOM
  def Ï     = (INT ^^ {CInt(_)}).|(l ^^ {Cx(_)})
  def σ     : Parser[σ]
            = (σ1 ~ "->" ~ σ                  ^^ {case a~_~b=>tarr(a,b)}).
            | (σ1)
  def σ1    = b.
            | ("{" ~> repsep(lσ,",") <~ "}"   ^^ {r => trecord(r)}).
            | ("<" ~> repsep(lσ,",") <~ ">"   ^^ {r => tvariant(r)}).
            | ("∀" ~ t ~ "::" ~ k ~ "." ~ σ  ^^ {case _~t~_~k~_~σ => ∀(t,k,σ)}).
            | ("idx" ~>"(" ~>t ~("," ~>σ<~")")~("=>"~>σ)
                                              ^^ {case t~σ1~σ2 => idx(t,σ1,σ2)}).
            | (t ^^ {a=>tx(a)}).
            | ("("~> σ <~")")
  def lσ    = l ~ ":" ~ σ                     ^^ {case a~_~b=>(a,b)}
  def k     = ("U"                            ^^ {_=>U}).
            | ("{{" ~> repsep(lσ,",") <~ "}}" ^^ {r => krecord(r)}).
            | ("<<" ~> repsep(lσ,",") <~ ">>" ^^ {r => kvariant(r)})
  def i     = INT                             ^^ {i=>CInt(i)}
  def cb    = ("true"                         ^^ {_=>CTrue}).
            | ("false"                        ^^ {_=>CFalse}).
            | (i)
  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})

  def c     : Parser[C]
            = (rep1(c1)                       ^^ {cs=>cs.reduceLeft{CApp}})
  def c1    = (c2 ~ rep("["~> Ï <~"]")        ^^ {case c~ls=>ls.foldLeft(c){CDot}})
  def c2    = (x                              ^^ {Cx(_)}).
            | (cb).
            | ("λ" ~ x ~ "." ~ c              ^^ {case _~x~_~c=>CAbs(x,c)}).
            | ("{" ~> repsep(c,",") <~ "}"    ^^ {r => CRecord(r)}).
            | ("<" ~> Ï ~ "=" ~ c <~ ">"      ^^ {case (l~_~c) => CVariant(l,c)}).
            | ("switch"~c~"of"~repsep(c,",")  ^^ {case _~c~_~cs=>CSwitch(c,cs)}).
            | ("modify"~>"("~>c~","~Ï~","~c<~")"
                                              ^^ {case c~_~i~_~c2=>CModify(c,i,c2)}).
            | ("let"~>x~"="~c~"in"~c          ^^ {case x~_~c~_~c2=>CLet(x,c,c2)}).
            | ("("~>c<~")"                    ^^ {case c=>c})

  def parseC(s:String):C = {
    parseAll(c, s) match {
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
