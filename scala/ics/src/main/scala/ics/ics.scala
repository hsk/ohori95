// implementation calculs system
package ics

object ics {
  import mss2._

  trait C
  case object CTrue extends C
  case object CFalse extends C
  case class CInt(v:Int) extends C
  case class Cx(v:x) extends C
  case class CAbs(x:x,C:C) extends C
  case class CApp(c1:C,c2:C) extends C
  case class CLet(x:x,c1:C,c2:C) extends C
  case class CRecord(f:List[C]) extends C
  case class CDot(C:C,l:C) extends C
  case class CModify(C:C,l:C,C2:C) extends C
  case class CVariant(l:C,C:C) extends C
  case class CSwitch(C:C,w:List[C]) extends C

  def v(c:C):Boolean = c match {
    case c if cb(c) => true
    case CAbs(x,_) => true
    case CRecord(cs) => !cs.exists{case(c)=> !v(c)}
    case CVariant(l,c) => v(c)
    case _ => false
  }

  def i(c:C)   = c match {case CInt(_) => true case _ => false}
  def cb(c:C)  = c match {case CTrue => true case CFalse => true case _ => i(c)}
  def x(c:C)   = c match {case Cx(_)=>true case _=>false}
  def c(c:Any) = c match {case _:C=>true case _=>false}

  def evHole(c:C):(C,C=>C) = c match {
    case CApp(c1,c2) if !v(c1) =>
      evHole(c1) match {case(c,h)=>(c,{c=>CApp(h(c),c2)})}
    case CApp(v1,c2) if !v(c2) =>
      evHole(c2) match {case(c,h)=>(c,{c=>CApp(v1,h(c))})}
    case CLet(x,c1,c2) if !v(c1) =>
      evHole(c1) match {case(c,h)=>(c,{c=>CLet(x,h(c),c2)})}
    case CRecord(cs) =>
      def find(hs:List[C],ls:List[C]):(C,C=>C) = ls match {
        case List() => (c,{c=>c})
        case c::ls if !v(c) =>
          evHole(c)match{case (c,h)=>(c,{c=>CRecord(hs.reverse:::h(c)::ls)})}
        case c::ls => find(c::hs,ls)
      }
      find(List(),cs)
    case CDot(c,l) if !v(c) =>
      evHole(c) match{case(c,h)=>(c,{c=>CDot(h(c),l)})}
    case CModify(c1,l,c2) if !v(c1) =>
      evHole(c1) match{case(c,h)=>(c,{c=>CModify(h(c),l,c2)})}
    case CModify(v1,l,c2) if !v(c2) =>
      evHole(c2) match{case(c,h)=>(c,{c=>CModify(v1,l,h(c))})}
    case CVariant(l,c) if !v(c) =>
      evHole(c) match{case(c,h)=>(c,{c=>CVariant(l,h(c))})}
    case CSwitch(c,cs) if !v(c) =>
      evHole(c) match{case(c,h)=>(c,{c=>CSwitch(h(c),cs)})}
    case c => (c,{c=>c})
  }

  def ev1(c:C):C = {
    c match {
    case CApp(CAbs(x,c),v1) if v(v1) => csub(Map(x->v1),c)
    case CDot(CRecord(vs),CInt(i)) => vs(i-1)
    case CModify(CRecord(vs),CInt(i),v) =>
      def find(hs:List[C],l:Int,ls:List[C]):C = ls match {
        case List() => CRecord(hs.reverse)
        case c::ls if l==i => CRecord(hs.reverse:::v::ls)
        case c::ls => find(c::hs,l+1,ls)
      }
      find(List(),1,vs)
    case CSwitch(CVariant(CInt(li),v),ls) => CApp(ls(li-1),v)
    case CLet(x,v,c) => csub(Map(x->v),c)
    case c => throw new Exception("error")
    }
  }

  def eval1(c:C):C = try {
    val (c1,f)=evHole(c)
    println("ctx="+c1)
    f(ev1(c1))
  } catch {
    case _:Throwable => ev1(c)
  }

  def eval(c:C):C = try {
    println(c)
    eval(eval1(c))
  } catch {
    case _:Throwable => c
  }

  def csub(S:Map[x,C],c:C):C = c match {
    case Cx(x) if S.contains(x) => csub(S,S(x))
    case Cx(x) => Cx(x)
    case c if cb(c) => c
    case CAbs(x,c) => CAbs(x,csub(S - x,c))
    case CApp(c1,c2) => CApp(csub(S,c1),csub(S,c2))
    case CRecord(cs) => CRecord(cs.map{(c)=>csub(S,c)})
    case CDot(c,l) => CDot(csub(S,c),csub(S,l))
    case CModify(c1,l,c2) => CModify(csub(S,c1),csub(S,l),csub(S,c2))
    case CVariant(l,c) => CVariant(l,csub(S,c))
    case CSwitch(c,cs) => CSwitch(csub(S,c),cs.map{(c)=>csub(S,c)})
    case CLet(x,c1,c2) => CLet(x,csub(S,c1),csub(S-x,c2))
  }

  // ------------------------------
  // compiler
  // ------------------------------

  def kinding(K:Map[σ,k],σ:σ):k = σ match {
    case t if K.contains(t) => K(σ)
    case trecord(f) => krecord(f)
    case tvariant(f) => kvariant(f)
    case _ => U
  }

  def idxSet(t:σ,k:k):Set[(x,σ)] = k match {
    case U => Set()
    case krecord(f) => f.map{case(l,_)=>(l,t)}.toSet
    case kvariant(f) => f.map{case(l,_)=>(l,t)}.toSet
  }

  def idxSet(σ:σ):Set[(x,σ)] = σ match {
    case ∀(t,k,τ) => idxSet(tx(t),k) ++ idxSet(τ)
    case _ => Set()
  }

  def idxSet(K:Map[σ,k]):Set[(x,σ)] =
    K.foldLeft(Set[(x,σ)]()) {
      case (is1,(t,k)) => is1 ++ idxSet(t,k)
    }

  def xts(m:M,ts:List[σ]):(M,List[σ]) = m match {
    case MTApp(m,t) => xts(m,t::ts)
    case c => (c,ts) 
  }

  def getT(σ:σ):(List[(x,k)],σ) = σ match {
    case ∀(ti,U,t) => getT(t) match {case(l,t1)=>((ti->U)::l,t1)}
    case ∀(ti,krecord(ks),t) => getT(t) match {case(l,t1)=>((ti->krecord(ks.sortWith{case((l1,_),(l2,_))=>l1<l2}))::l,t1)}
    case ∀(ti,kvariant(ks),t) => getT(t) match {case(l,t1)=>((ti->kvariant(ks.sortWith{case((l1,_),(l2,_))=>l1<l2}))::l,t1)}
    case t => (List(),t)
  }

  def getL(L:List[(x,(x,σ))],σ:σ):(List[(x,(x,σ))],List[x]) = σ match {
    case idx(li,ti,t) =>
      val ii = fresh()
      val (l_,is) = getL(L,t)
      ((ii->(li,ti))::l_,ii::is)
    case _ => (L,List())
  }

  case class idx(x:x,t:σ,t2:σ) extends σ

  def rep(σ:σ):σ = σ match {
    case trecord(lts) => trecord(lts.map{case(x,t)=>(x,rep(t))})
    case tvariant(lts) => tvariant(lts.map{case(x,t)=>(x,rep(t))})
    case ∀(_,_,_) =>
      val (l,t) = getT(σ)
      val t2 = l.foldRight(rep(t)){
        case((x,U),t)=>t
        case((x,krecord(f)),t)=> f.foldRight(t){case((li,ti),t1)=>idx(li,tx(x),t1)}
        case((x,kvariant(f)),t)=> f.foldRight(t){case((li,ti),t1)=>idx(li,tx(x),t1)}
      }
      l.foldRight(t2) {case((t,k),t3)=> ∀(t,k,t3)}
    case t => t
  }

  def addλ(l:List[x],c:C):C = l match {
    case List() => c
    case ii::is => CAbs(ii,addλ(is,c))
  }

  def mks(σ:σ,τs:List[σ]):(Map[x,σ],σ) = (σ,τs) match {
    case (σ,List()) => (Map(),σ)
    case (∀(t,_,σ),τ::τs) => val(s,σ_) =mks(σ,τs); (s+(t->τ),σ_)
    case (_,_) => throw new Exception("assert")
  }

  def cdot(L:List[(x,(x,σ))],S:Map[x,σ],xi:C,σ:σ):C = σ match {
    case idx(l,t,t2) =>
      val τ = tsub(S,t)
      val ks = kinding(Map(),τ)
      val idxs = idxSet(τ,ks).toList.zipWithIndex
      val ci = idxs.find {
        case ((l1,τ1),i) => l==l1 && τ==τ1
      } match {
        case Some((_,i)) => CInt(i+1)
        case None =>
          L.find{case(x,(l1,τ1))=>l==l1 && τ==τ1} match {
            case Some((x,_)) => Cx(x)
            case None => throw new Exception("assert find index")
          }
      }
      cdot(L,S,CApp(xi,ci),t2)
    case _ => xi
  }

  def c(L:List[(x,(x,σ))],T:Map[x,σ],M:M):C = M match {
    case Mx(x) => Cx(x)
    case MTApp(x1,τ1) =>
      val (Mx(x),τs) = xts(M,List())
      val σ = T(x)
      val (s,σ_) = mks(σ,τs)
      cdot(L,s,Cx(x),σ_)
    case MTrue => CTrue
    case MFalse => CFalse
    case MInt(i) => CInt(i)
    case MAbs(x,τ,m) => CAbs(x,c(L,T+(x->τ),m))
    case MApp(m1,m2) => CApp(c(L,T,m1),c(L,T,m2))
    case MRecord(f) => CRecord(f.map{case(_,m) => c(L,T,m)})
    case MDot(m1,τ,l) =>
      val c1 = c(L,T,m1)
      val ks = kinding(Map(),τ)
      val idxs = idxSet(τ,ks).toList.zipWithIndex
      val ci = idxs.find {
        case ((l1,τ1),i) => l==l1 && τ==τ1
      } match {
        case Some((_,i)) => CInt(i+1)
        case None =>
          L.find{case(x,(l1,τ1))=>l==l1 && τ==τ1} match {
            case Some((x,_)) => Cx(x)
            case None => throw new Exception("assert find index")
          }
      }
      CDot(c1,ci)
    case MModify(m1,τ,l,m2) =>
      val c1 = c(L,T,m1)
      val c2 = c(L,T,m2)
      val ks = kinding(Map(),τ)
      val idxs = idxSet(τ,ks).toList.zipWithIndex
      val ci = idxs.find {
        case ((l1,τ1),i) => l==l1 && τ==τ1
      } match {
        case Some((_,i)) => CInt(i+1)
        case None =>
          L.find{case(x,(l1,τ1))=>l==l1 && τ==τ1} match {
            case Some((x,_)) => Cx(x)
            case None => throw new Exception("assert find index")
          }
      }
      CModify(c1,ci,c2)
    case MVariant(l,m,τ) =>
      val c1 = c(L,T,m)
      val idxs = idxSet(τ,kinding(Map(), τ)).toList.zipWithIndex
      val ci = idxs.find {
        case ((l1,τ1),i) => l==l1 && τ==τ1
      } match {
        case Some((_,i)) => CInt(i+1)
        case None =>
          L.find{case(x,(l1,τ1))=>l==l1 && τ==τ1} match {
            case Some((x,_)) => Cx(x)
            case None => throw new Exception("assert find index")
          }
      }
      CVariant(ci,c1)
    case MCase(m,f) =>
      val c1 = c(L,T,m)
      CSwitch(c1,f.map{case(li,mi)=>c(L,T,mi)})
    case MPoly(m1,t) => val (_,idxs) = getT(rep(t)); val (l_,is) = getL(L,idxs); addλ(is,c(l_,T,m1))
    case MLet(x,σ,m1,m2) => CLet(x,c(L,T,m1),c(L,T+(x->rep(σ)),m2))
  }

  def lk(K:Map[σ,k]):List[(x,(x,σ))] =
    idxSet(K).toList.map{case(l,t)=>(fresh(),(l,t))}
}
