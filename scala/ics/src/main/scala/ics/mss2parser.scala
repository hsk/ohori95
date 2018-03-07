package ics
import util.parsing.combinator._

object mss2parser extends RegexParsers {
  import mss2._
  val keywords = Set("true","false","case","of","modify","Poly","let","in")

  def ATOM  = """[a-zA-Z_][a-zA-Z0-9_]*""".r
  def INT   = """-?[0-9]+""".r                ^^ { case a     => a.toInt }
  def t     = """[a-zA-Z_][a-zA-Z0-9_]*""".r  ^? { case a if !(a == "true" && a == "false") => a }
  def b     = ("int"                          ^^ {case _ => tint}).
            | ("bool"                         ^^ {case _=> tbool})
  def l     = ATOM
  def σ     : Parser[σ]
            = (σ1 ~ "->" ~ σ                  ^^ {case a~_~b=>tarr(a,b)}).
            | (σ1)
  def σ1    = b.
            | (t ^^ {a=>tx(a)}).
            | ("{" ~> repsep(lσ,",") <~ "}"   ^^ {r => trecord(r)}).
            | ("<" ~> repsep(lσ,",") <~ ">"   ^^ {r => tvariant(r)}).
            | ("∀" ~ t ~ "::" ~ k ~ "." ~ σ  ^^ {case _~t~_~k~_~σ => ∀(t,k,σ)}).
            | ("("~> σ <~")")
  def lσ    = l ~ ":" ~ σ                     ^^ {case a~_~b=>(a,b)}
  def k     = ("U"                            ^^ {_=>U}).
            | ("{{" ~> repsep(lσ,",") <~ "}}" ^^ {r => krecord(r)}).
            | ("<<" ~> repsep(lσ,",") <~ ">>" ^^ {r => kvariant(r)})
  def i     = INT                             ^^ {i=>EInt(i)}
  def cb    = ("true"                         ^^ {_=>ETrue}).
            | ("false"                        ^^ {_=>EFalse}).
            | (i)
  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})

  def e     : Parser[E]
            = (rep1(e1)                       ^^ {es=>es.reduceLeft{EApp}})
  def e1    = (e2 ~ rep("#" ~> l)             ^^ {case e~ls=>ls.foldLeft(e){EDot}})
  def e2    = (x                              ^^ {Ex(_)}).
            | (cb).
            | ("λ" ~ x ~ "." ~ e              ^^ {case _~x~_~e=>EAbs(x,e)}).
            | ("{" ~> repsep(le,",") <~ "}"   ^^ {r => ERecord(r)}).
            | ("<" ~> le <~ ">"               ^^ {case (l,e) => EVariant(l,e)}).
            | ("case"~e~"of"~"<"~repsep(le,",")~">"
                                              ^^ {case _~e~_~_~les~_=>ECase(e,les)}).
            | ("modify"~>"("~>e~","~l~","~e<~")"
                                              ^^ {case e~_~l~_~e2=>EModify(e,l,e2)}).
            | ("let"~>x~"="~e~"in"~e          ^^ {case x~_~e~_~e2=>ELet(x,e,e2)}).
            | ("("~>e<~")"                    ^^ {case e=>e})
  def le    = l ~ "=" ~ e                     ^^ {case a~_~b=>(a,b)}

  def mi    = INT                             ^^ {i=>MInt(i)}
  def mcb   = ("true"                         ^^ {_=>MTrue}).
            | ("false"                        ^^ {_=>MFalse}).
            | (mi)

  def M     : Parser[M]
            = (rep1(M1)                       ^^ {ms=>ms.reduceLeft{MApp}})
  def M1    = (M2 ~ rep(":" ~> σ ~ ("#" ~> l))^^ {case m~ls=>ls.foldLeft(m){case(m,(σ~l))=>MDot(m,σ,l)}})
  
  def M2    = (M3 ~ rep("!" ~> σ)             ^^ {case m~σs=>σs.foldLeft(m){MTApp}})
  def M3    = (x                              ^^ {Mx(_)}).
            | (mcb).
            | ("λ" ~ x ~ ":" ~ σ ~ "." ~ M    ^^ {case _~x~_~σ~_~m=>MAbs(x,σ,m)}).
            | ("{" ~> repsep(lM,",") <~ "}"   ^^ {r => MRecord(r)}).
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
