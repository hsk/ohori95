// Second-Order System Λ∀,#
object sos2 {
  // Syntaxs

  type l = String
  type x = String

  trait k
  case object U extends k
  case class krecord(v:List[(l,σ)]) extends k
  case class kvariant(v:List[(l,σ)]) extends k

  trait σ
  case object tbool extends σ
  case object tint extends σ
  case class tx(v:String) extends σ
  case class tarr(v1:σ,v2:σ) extends σ
  case class trecord(v:List[(l,σ)]) extends σ
  case class tvariant(v:List[(l,σ)]) extends σ
  case class ∀(t:x,k:k,σ:σ) extends σ

  def t(t:σ) = t match {case tx(_)=>true case _=>false}
  def b(t:σ) = t == tbool || t == tint
  def q(a:Any) = a match {case _:σ => true case _ => false}
  def k(a:Any) = a match {case _:k => true case _ => false}

  trait M
  case object MTrue extends M
  case object MFalse extends M
  case class MInt(v:Int) extends M
  case class Mx(v:String) extends M
  case class MAbs(x:String,σ:σ,M:M) extends M
  case class MApp(M1:M,M2:M) extends M
  case class MTλ(t:String,k:k,M:M) extends M
  case class MTApp(M1:M,σ:σ) extends M
  case class MRecord(v:List[(l,M)]) extends M
  case class MDot(M:M,l:l) extends M
  case class MModify(M:M,l:l,M2:M) extends M
  case class MVariant(l:l,M:M,σ:σ) extends M
  case class MCase(M:M,w:List[(l,M)]) extends M
  
  def i(m:M)   = m match {case MInt(_) => true case _ => false}
  def cb(m:M)  = m match {case MTrue => true case MFalse => true case _ => i(m)}
  def x(m:M)   = m match {case Mx(_)=>true case _=>false}
  def m(m:Any) = m match {case _:M=>true case _=>false}

  // Substitutions
  def tsub(S:Map[x,σ],σ:σ):σ = σ match {
    case tx(x) if S.contains(x) => tsub(S,S(x))
    case tx(x) => tx(x)
    case _ if b(σ) => σ
    case tarr(σ1,σ2) => tarr(tsub(S,σ1),tsub(S,σ1))
    case trecord(lMs) => trecord(lMs.map{case(l,t)=>(l,tsub(S,t))})
    case tvariant(lMs) => tvariant(lMs.map{case(l,t)=>(l,tsub(S,t))})
    case ∀(t,k,σ) => ∀(t,ksub(S-t,k),tsub(S-t,σ))
  }
  def ksub(S:Map[x,σ],k:k):k = k match {
    case U => U
    case krecord(lMs) => krecord(lMs.map{case(l,t)=>(l,tsub(S,t))})
    case kvariant(lMs) => kvariant(lMs.map{case(l,t)=>(l,tsub(S,t))})
  }
  def msub(S:Map[x,M],M:M):M = M match {
    case Mx(x) if S.contains(x) => msub(S,S(x))
    case Mx(x) => Mx(x)
    case m if cb(m) => m
    case MAbs(x,σ,m) => MAbs(x,σ,msub(S - x,m))
    case MApp(m1,m2) => MApp(msub(S,m1),msub(S,m2))
    case MTApp(m,σ) => MTApp(msub(S,m),σ)
    case MTλ(t,k,m) => MTλ(t,k,msub(S,m))
    case MRecord(lms) => MRecord(lms.map{case(l,m)=>(l,msub(S,m))})
    case MDot(m,l) => MDot(msub(S,m),l)
    case MModify(m1,l,m2) => MModify(msub(S,m1),l,msub(S,m2))
    case MVariant(l,m,σ) => MVariant(l,msub(S,m),σ)
    case MCase(m,lMs) => MCase(msub(S,m),lMs.map{case(l,m)=>(l,msub(S,m))})
  }
  def mtsub(S:Map[x,σ],M:M):M = M match {
    case MAbs(x,σ,m) => MAbs(x,tsub(S,σ),mtsub(S,m))
    case MApp(m1,m2) => MApp(mtsub(S,m1),mtsub(S,m2))
    case MTApp(m,σ) => MTApp(mtsub(S,m),tsub(S,σ))
    case MTλ(t,k,m) => MTλ(t,ksub(S-t,k),mtsub(S-t,m)) // todo to prolog
    case MRecord(lMs) => MRecord(lMs.map{case(l,m)=>(l,mtsub(S,m))})
    case MDot(m,l) => MDot(mtsub(S,m),l)
    case MModify(m1,l,m2) => MModify(mtsub(S,m1),l,mtsub(S,m2))
    case MVariant(l,m,σ) => MVariant(l,mtsub(S,m),tsub(S,σ))
    case MCase(m,lMs) => MCase(mtsub(S,m),lMs.map{case(l,m)=>(l,mtsub(S,m))})
    case _ => M
  }

  // Reduction rules
  def eval1(M:M):M = M match {
    case MApp(MAbs(x,_,m),n) => msub(Map(x->n),m)       // (β)
    case MTApp(MTλ(t,_,m),σ) => mtsub(Map(t->σ), m)   // (type-β)
    case MDot(MRecord(lMs),li) => lMs.toMap.apply(li) // (dot)
    case MModify(MRecord(lMs),l,m) => MRecord(lMs.map{case(li,mi)=>(li,if(l==li)m else mi)})// (modify)
    case MCase(MVariant(li,m,_),lMs) => MApp(lMs.toMap.apply(li),m) // (case)
    case MApp(m,n) => MApp(eval1(m),n)
    case MTApp(m,σ) => MTApp(eval1(m),σ)
    case MModify(m,l,n) => MModify(eval1(m),l,n)
    case MCase(m,lMs) => MCase(eval1(m),lMs)
  }

  def eval(m:M):M = try {
    eval(eval1(m))
  } catch {
    case _:Throwable => m
  }

  // Kinding rules
  def toK(K:Map[x,k],σ:σ):k = σ match {
    case tx(x) =>
      K.get(x) match {
        case Some(k) => k
        case None => U
      }
    case trecord(lts) => krecord(lts)
    case tvariant(lts) => kvariant(lts)
    case _ => U
  }
  def containsK(K:Map[x,k],σ:σ,k2:k) = (toK(K,σ),k2) match {
    case (_,U) => true
    case (krecord(lts1),krecord(lts2)) => lts1.toSet ++ lts2.toSet == lts1.toSet
    case (kvariant(lts1),kvariant(lts2)) => lts1.toSet ++ lts2.toSet == lts1.toSet
    case (_,_) => false
  }

  // Type system
  def ti(K:Map[x,k],T:Map[x,σ],M:M):σ = M match {
    case Mx(x)   => T(x)  // VAR
    case MInt(i) => tint  // CONST
    case MTrue   => tbool // CONST
    case MFalse  => tbool // CONST
    case MAbs(x,σ1,m2) => // ABS
      val σ2 = ti(K,T+(x->σ1),m2)
      tarr(σ1,σ2)
    case MApp(m1,m2) => // APP
      val σ = ti(K,T,m1)
      σ match {
        case tarr(σ1,σ2) =>
          if (σ1 != ti(K,T,m2)) throw new Exception("error")
          σ2
        case _ => throw new Exception("error")
      }
    case MTλ(t,k,m) => // TABS
      val σ = ti(K+(t->k),T,m)
      ∀(t,k,σ)
    case MTApp(m,σ2) => // TAPP
      val σ1 = ti(K,T,m)
      σ1 match {
        case ∀(t,k,σ1) =>
          if(!containsK(K,σ2,k)) throw new Exception("kind error")
          tsub(Map(t->σ2),σ1)
        case _ => throw new Exception("error")
      }
    case MRecord(lMs) => // RECORD
      trecord(lMs.map{case(li,mi)=>(li,ti(K,T,mi))})
    case MDot(m, l) => // DOT
      val σ1 = ti(K,T,m)
      toK(K,σ1) match {
        case krecord(lts) => lts.toMap.apply(l)
        case _ => throw new Exception("error")
      }
    case MModify(m1,l,m2) => // MODIFY
      val σ1 = ti(K,T,m1)
      val σ2 = ti(K,T,m2)
      if (!containsK(K,σ1,krecord(List(l->σ2)))) throw new Exception("error")
      σ1
    case MVariant(l,m,σ2) => // VARIANT
      val σ1=ti(K,T,m)
      if (!containsK(K,σ2,kvariant(List(l->σ1)))) throw new Exception("error")
      σ2
    case MCase(m,lMs) => // CASE
      val t1 = ti(K,T,m)
      lMs.map{case(li,mi)=>(li,ti(K,T,mi))} match {
        case lts @ (_,tarr(_,σ))::_ =>
          val lts2 = lts.map {
            case(li,tarr(σi,σ_))=>
              if(σ != σ_) throw new Exception("error")
              (li,σi)
            case (_,_) => throw new Exception("error")
          }
          if(!containsK(K,tvariant(lts2),toK(K,t1))) throw new Exception("error")
          σ
        case _ => throw new Exception("error")
      }
  }
}
