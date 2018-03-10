// implementation calculs system
package ics

object ics {
  import tmss._

  sealed trait c
  case object CTrue extends c
  case object CFalse extends c
  case class CInt(v:Int) extends c
  case class Cx(v:x) extends c
  case class CAbs(x:x, c:c) extends c
  case class CApp(c1:c, c2:c) extends c
  case class CLet(x:x, c1:c, c2:c) extends c
  case class CRecord(f:List[c]) extends c
  case class CDot(c:c, l:c) extends c
  case class CModify(c:c, l:c, c2:c) extends c
  case class CVariant(l:c, c:c) extends c
  case class CSwitch(c:c, w:List[c]) extends c

  // ------------------------------
  // compiler
  // ------------------------------

  def kinding(eK:Map[q,k], q:q):k = q match {
    case q if eK.contains(q) => eK(q)
    case TRecord(f) => KRecord(f)
    case TVariant(f) => KVariant(f)
    case _ => U
  }

  def idxSet(t:q, k:k):Set[(x,q)] = k match {
    case U => Set()
    case KRecord(f) => f.map{case(l,_)=>(l,t)}.toSet
    case KVariant(f) => f.map{case(l,_)=>(l,t)}.toSet
  }
  /*
  def idxSet1(q:q):Set[(x,q)] = q match {
    case ∀(x,k,t) => idxSet(tx(x),k) ++ idxSet(t)
    case _ => Set()
  }
  */
  def idxSetK(eK:Map[q,k]):Set[(x,q)] =
    eK.foldLeft(Set[(x,q)]()) {
      case (is1,(t,k)) => is1 ++ idxSet(t,k)
    }

  def sortf(f:List[(x,q)]):List[(x,q)] = f.sortWith{case((l1,_),(l2,_))=>l1<l2}
  def sortk(k:k):k = k match {
    case U => U
    case KRecord(f) => KRecord(sortf(f))
    case KVariant(f) => KVariant(sortf(f))
  }
  def sortq(q:q):(List[(x,k)],q) = q match {
    case TAll(ti,k,t) => val (l,t1) = sortq(t); (ti->sortk(k)::l,t1)
    case t => (List(),t)
  }

  def addIdx(q:q):q = q match {
    case TRecord(lts) => TRecord(lts.map{case(x,t)=>(x,addIdx(t))})
    case TVariant(lts) => TVariant(lts.map{case(x,t)=>(x,addIdx(t))})
    case TAll(_,_,_) =>
      val (l,t) = sortq(q)
      val t2 = l.foldRight(addIdx(t)){
        case((x,U),t)=>t
        case((x,KRecord(f)),t)=> f.foldRight(t){case((li,ti),t1)=>TIdx(li,Tx(x),t1)}
        case((x,KVariant(f)),t)=> f.foldRight(t){case((li,ti),t1)=>TIdx(li,Tx(x),t1)}
      }
      l.foldRight(t2) {case((t,k),t3)=> TAll(t,k,t3)}
    case t => t
  }

  def getci(eL:List[(x,(x,q))], l:x, t:q):c = {
    val idxs = idxSet(t, kinding(Map(), t)).toList.zipWithIndex
    idxs.find { case ((l1, t1), i) => l == l1 && t == t1 } match {
      case Some((_, i)) => CInt(i + 1)
      case None =>
        eL.find { case (x, (l1, t1)) => l == l1 && t == t1 } match {
          case Some((x, _)) => Cx(x)
          case None => throw new Exception("assert find index")
        }
    }
  }

  def c(eL:List[(x,(x,q))], eT:Map[x,q], m:m):c = m match {
    case Mx(x) => Cx(x)
    case MTApp(Mx(x),ts) =>
      def stripq(ts:List[q], q:q):(Map[x,q],q) = (ts,q) match {
        case (List(),q) => (Map(),q)
        case (t::ts,TAll(x,_,q)) => val(s,q_) = stripq(ts,q); (s+(x->t),q_)
        case (_,_) => throw new Exception("assert stripq"+(q,ts))
      }
      def addApp(eL:List[(x,(x,q))], s:Map[x,q], q:q, c:c):c = q match {
        case TIdx(l,t,t2) => addApp(eL,s,t2,CApp(c,getci(eL,l,tsub(s,t))))
        case _ => c
      }
      val (s,t) = stripq(ts,eT(x)); addApp(eL,s,t,Cx(x))
    case MTrue => CTrue
    case MFalse => CFalse
    case MInt(i) => CInt(i)
    case MAbs(x,t,m) => CAbs(x,c(eL,eT+(x->t),m))
    case MApp(m1,m2) => CApp(c(eL,eT,m1),c(eL,eT,m2))
    case MRecord(f) => CRecord(f.map{case(_,m) => c(eL,eT,m)})
    case MDot(m1,t,l) => CDot(c(eL,eT,m1),getci(eL,l,t))
    case MModify(m1,t,l,m2) => val c1 = c(eL,eT,m1); CModify(c1,getci(eL,l,t),c(eL,eT,m2))
    case MVariant(l,m,t) => CVariant(getci(eL,l,t),c(eL,eT,m))
    case MCase(m,f) => CSwitch(c(eL,eT,m),f.map{case(li,mi)=>c(eL,eT,mi)})
    case MPoly(m1,t) =>
      def getL(eL:List[(x,(x,q))], q:q):(List[(x,(x,q))],List[x]) = q match {
        case TIdx(l,ti,t) => val x = fresh(); val (eL_,is) = getL(eL,t); ((x->(l,ti))::eL_,x::is)
        case _ => (eL,List())
      }
      val (_,idxs) = sortq(addIdx(t))
      val (eL_,is) = getL(eL,idxs)
      is.foldRight(c(eL_,eT,m1)){(x,c)=>CAbs(x,c)}
    case MLet(x,q,m1,m2) => CLet(x,c(eL,eT,m1),c(eL,eT+(x->addIdx(q)),m2))
  }

  def lk(eK:Map[q,k]):List[(x,(x,q))] =
    idxSetK(eK).toList.map{case(l,t)=>(fresh(),(l,t))}

  // ------------------------------
  // evaluator
  // ------------------------------

  def v(c:c):Boolean = c match {
    case CInt(_) => true
    case CTrue => true
    case CFalse => true
    case CAbs(x,_) => true
    case CRecord(cs) => !cs.exists{case(c)=> !v(c)}
    case CVariant(l,c) => v(c)
    case _ => false
  }

  def csub(s:Map[x,c], c:c):c = c match {
    case Cx(x) if s.contains(x) => csub(s,s(x))
    case CAbs(x,c) => CAbs(x,csub(s - x,c))
    case CApp(c1,c2) => CApp(csub(s,c1),csub(s,c2))
    case CRecord(cs) => CRecord(cs.map{(c)=>csub(s,c)})
    case CDot(c,l) => CDot(csub(s,c),csub(s,l))
    case CModify(c1,l,c2) => CModify(csub(s,c1),csub(s,l),csub(s,c2))
    case CVariant(l,c) => CVariant(l,csub(s,c))
    case CSwitch(c,cs) => CSwitch(csub(s,c),cs.map{(c)=>csub(s,c)})
    case CLet(x,c1,c2) => CLet(x,csub(s,c1),csub(s-x,c2))
    case _ => c
  }

  def eval1(c:c):c = c match {
    case CApp(c1,c2) if !v(c1) => CApp(eval1(c1),c2)
    case CApp(v1,c2) if !v(c2) => CApp(v1,eval1(c2))
    case CLet(x,c1,c2) if !v(c1) => CLet(x,eval1(c1),c2)
    case CRecord(cs) =>
      def find(hs:List[c], ls:List[c]):c = ls match {
        case List() => throw new Exception("error")
        case c::ls if !v(c) => CRecord(hs.reverse:::eval1(c)::ls)
        case c::ls => find(c::hs,ls)
      }
      find(List(),cs)
    case CDot(c,l) if !v(c) => CDot(eval1(c),l)
    case CModify(c1,l,c2) if !v(c1) => CModify(eval1(c1),l,c2)
    case CModify(v1,l,c2) if !v(c2) => CModify(v1,l,eval1(c2))
    case CVariant(l,c) if !v(c) => CVariant(l,eval1(c))
    case CSwitch(c,cs) if !v(c) => CSwitch(eval1(c),cs)

    case CApp(CAbs(x,c),v1) => csub(Map(x->v1),c)
    case CDot(CRecord(vs),CInt(i)) => vs(i-1)
    case CModify(CRecord(vs),CInt(i),v) =>
      def find(hs:List[c], l:Int, ls:List[c]):c = ls match {
        case List() => throw new Exception("error")
        case c::ls if l==i => CRecord(hs.reverse:::v::ls)
        case c::ls => find(c::hs,l+1,ls)
      }
      find(List(),1,vs)
    case CSwitch(CVariant(CInt(li),v),ls) => CApp(ls(li-1),v)
    case CLet(x,v,c) => csub(Map(x->v),c)
    case c => throw new Exception("error")
  }

  def eval(c:c):c = try {
    eval(eval1(c))
  } catch {
    case _:Throwable => c
  }

}
