// ML-Style System λlet,#

package mss

object mss {

  // Syntaxs

  type l = String
  type x = String

  trait e
  case object ETrue extends e
  case object EFalse extends e
  case class EInt(v: Int) extends e
  case class Ex(v: x) extends e
  case class EAbs(x: x, e: e) extends e
  case class EApp(M1: e, M2: e) extends e
  case class ERecord(v: List[(l, e)]) extends e
  case class EDot(e: e, l: l) extends e
  case class EModify(e: e, l: l, e2: e) extends e
  case class EVariant(l: l, e: e) extends e
  case class ECase(e: e, w: List[(l, e)]) extends e
  case class ELet(x: x, e1: e, e2: e) extends e

  def v(e: e): Boolean = e match {
    case EInt(_) => true
    case ETrue => true
    case EFalse => true
    case EAbs(x, _) => true
    case ERecord(les) => !les.exists { case (l, e) => !v(e) }
    case EVariant(l, e) => v(e)
    case _ => false
  }

  // Substitutions

  def esub(s: Map[x, e], e: e): e = e match {
    case Ex(x) if s.contains(x) => esub(s, s(x))
    case EAbs(x, e) => EAbs(x, esub(s - x, e))
    case EApp(e1, e2) => EApp(esub(s, e1), esub(s, e2))
    case ERecord(les) => ERecord(les.map { case (l, e) => (l, esub(s, e)) })
    case EDot(e, l) => EDot(esub(s, e), l)
    case EModify(e1, l, e2) => EModify(esub(s, e1), l, esub(s, e2))
    case EVariant(l, e) => EVariant(l, esub(s, e))
    case ECase(e, les) => ECase(esub(s, e), les.map { case (l, e) => (l, esub(s, e)) })
    case ELet(x, e1, e2) => ELet(x, esub(s, e1), esub(s, e2))
    case _ => e
  }

  // Reduction rules

  def eval1(e: e): e = e match {
    case EApp(e1, e2) if !v(e1) => EApp(eval1(e1), e2)
    case EApp(v1, e2) if !v(e2) => EApp(v1, eval1(e2))
    case ELet(x, e1, e2) if !v(e1) => ELet(x, eval1(e1), e2)
    case ERecord(les) =>
      def find(hs: List[(l, e)], ls: List[(l, e)]): e = ls match {
        case List() => throw new Exception("error")
        case (l, e) :: ls if !v(e) => ERecord(hs.reverse ::: (l, eval1(e)) :: ls)
        case (l, e) :: ls => find((l, e) :: hs, ls)
      }
      find(List(), les)
    case EDot(e, l) if !v(e) => EDot(eval1(e), l)
    case EModify(e1, l, e2) if !v(e1) => EModify(eval1(e1), l, e2)
    case EModify(v1, l, e2) if !v(e2) => EModify(v1, l, eval1(e2))
    case EVariant(l, e) if !v(e) => EVariant(l, eval1(e))
    case ECase(e, les) if !v(e) => ECase(eval1(e), les)

    case EApp(EAbs(x, e), v1) => esub(Map(x -> v1), e)
    case EDot(ERecord(lvs), li) => lvs.toMap.apply(li)
    case EModify(ERecord(lvs), li, v) =>
      def find(hs: List[(l, e)], ls: List[(l, e)]): e = ls match {
        case List() => throw new Exception("error")
        case (l, e) :: ls if l == li => ERecord(hs.reverse ::: (l, v) :: ls)
        case (l, e) :: ls => find((l, e) :: hs, ls)
      }
      find(List(), lvs)
    case ECase(EVariant(l, v), ls) => EApp(ls.toMap.apply(l), v)
    case ELet(x, v, e) => esub(Map(x -> v), e)
    case e => throw new Exception("error")
  }

  def eval(e: e): e = try {
    eval(eval1(e))
  } catch {
    case _: Throwable => e
  }

}
