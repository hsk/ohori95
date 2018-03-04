import util.parsing.combinator._

object sos2parser extends RegexParsers {
  import sos2._
  val keywords = Set("true","false","case","of","modify")

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
  def i     = INT                             ^^ {i=>MInt(i)}
  def cb    = ("true"                         ^^ {_=>MTrue}).
            | ("false"                        ^^ {_=>MFalse}).
            | (i)
  def x     = (ATOM                           ^? {case x if(!keywords.contains(x))=>x})
  def M     : Parser[M]
            = (rep1(M1)                       ^^ {ms=>ms.reduceLeft{MApp}})
  def M1    = (M2 ~ rep("#" ~> l)             ^^ {case m~ls=>ls.foldLeft(m){MDot}})
  def M2    = (M3 ~ rep("!" ~> σ)             ^^ {case m~σs=>σs.foldLeft(m){MTApp}})
  def M3    = (x                              ^^ {Mx(_)}).
            | (cb).
            | ("λ" ~ x ~ "::" ~ k ~ "." ~ M   ^^ {case _~x~_~k~_~m=>MTλ(x,k,m)}).
            | ("λ" ~ x ~ ":" ~ σ ~ "." ~ M    ^^ {case _~x~_~σ~_~m=>Mλ(x,σ,m)}).
            | ("{" ~> repsep(lM,",") <~ "}"   ^^ {r => MRecord(r)}).
            | ("<" ~> lM ~ ">" ~ ":" ~ σ      ^^ {case (l,m)~_~_~σ => MVariant(l,m,σ)}).
            | ("case"~M~"of"~"<"~repsep(lM,",")~">"
                                              ^^ {case _~m~_~_~lMs~_=>MCase(m,lMs)}).
            | ("modify"~>"("~>M~","~l~","~M<~")"
                                              ^^ {case m~_~l~_~m2=>MModify(m,l,m2)}).
            | ("("~M~")"                      ^^ {case _~m~_=>m})
  def lM    = l ~ "=" ~ M                     ^^ {case a~_~b=>(a,b)}

  def parsek(s:String):k = {
    parseAll(k, s) match {
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
