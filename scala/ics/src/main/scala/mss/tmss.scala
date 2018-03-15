// typed ML Style System

package mss

object tmss {
  type l = String
  type x = String
  trait k
  case object U extends k
  case class KRecord(v:List[(l,q)]) extends k
  case class KVariant(v:List[(l,q)]) extends k

  trait q
  case object TBool extends q
  case object TInt extends q
  case class Tx(v:String) extends q
  case class TArr(v1:q, v2:q) extends q
  case class TRecord(v:List[(l,q)]) extends q
  case class TVariant(v:List[(l,q)]) extends q
  case class TAll(t:x, k:k, q:q) extends q
  case class TIdx(x:x, t:q, t2:q) extends q

  trait m
  case class Mx(x:x) extends m
  case class MTApp(m1:m, qs:List[q]) extends m
  case object MTrue extends m
  case object MFalse extends m
  case class MInt(i:Int) extends m
  case class MAbs(x:x, q:q, m:m) extends m
  case class MApp(m1:m, m2:m) extends m
  case class MRecord(v:List[(l,m)]) extends m
  case class MDot(m:m, q:q, l:l) extends m
  case class MModify(m:m, q:q, l:l, m2:m) extends m
  case class MVariant(l:l, m:m, q:q) extends m
  case class MCase(m:m, w:List[(l,m)]) extends m
  case class MPoly(m:m, q:q) extends m
  case class MLet(x:x, q:q, m1:m, m2:m) extends m

  // Substitutions

  def ksub(s:Map[x,q], k:k):k = k match {
    case U => U
    case KRecord(f) => KRecord(f.map{case(l,t)=>(l,tsub(s,t))})
    case KVariant(f) => KVariant(f.map{case(l,t)=>(l,tsub(s,t))})
  }
  def tsub(s:Map[x,q], q:q):q = q match {
    case Tx(x) if s.contains(x) => tsub(s,s(x))
    case TArr(q1,q2) => TArr(tsub(s,q1),tsub(s,q2))
    case TRecord(f) => TRecord(f.map{case(l,t)=>(l,tsub(s,t))})
    case TVariant(f) => TVariant(f.map{case(l,t)=>(l,tsub(s,t))})
    case TAll(x,k,q) => TAll(x,ksub(s-x,k),tsub(s-x,q))
    case _ => q
  }
  def msub(s:Map[x,m], m:m):m = m match {
    case Mx(x) if s.contains(x) => msub(s,s(x))
    case MTApp(m,qs) => MTApp(msub(s,m),qs)
    case MAbs(x,q,m) => MAbs(x,q,msub(s - x,m))
    case MApp(m1,m2) => MApp(msub(s,m1),msub(s,m2))
    case MRecord(f) => MRecord(f.map{case(l,m)=>(l,msub(s,m))})
    case MDot(m,q,l) => MDot(msub(s,m),q,l)
    case MModify(m1,q,l,m2) => MModify(msub(s,m1),q,l,msub(s,m2))
    case MVariant(l,m,q) => MVariant(l,msub(s,m),q)
    case MCase(m,f) => MCase(msub(s,m),f.map{case(l,m)=>(l,msub(s,m))})
    case MPoly(m,q) => MPoly(msub(s,m),q)
    case MLet(x,q,m1,m2) => MLet(x,q,msub(s,m1),msub(s-x,m2))
    case _ => m
  }
  def mtsub(s:Map[x,q], m:m):m = m match {
    case MTApp(m,qs) => MTApp(mtsub(s,m),qs.map{q => tsub(s,q)})
    case MAbs(x,q,m) => MAbs(x,tsub(s,q),mtsub(s,m))
    case MApp(m1,m2) => MApp(mtsub(s,m1),mtsub(s,m2))
    case MRecord(lMs) => MRecord(lMs.map{case(l,m)=>(l,mtsub(s,m))})
    case MDot(m,q,l) => MDot(mtsub(s,m),tsub(s,q),l)
    case MModify(m1,q,l,m2) => MModify(mtsub(s,m1),tsub(s,q),l,mtsub(s,m2))
    case MVariant(l,m,q) => MVariant(l,mtsub(s,m),tsub(s,q))
    case MCase(m,lMs) => MCase(mtsub(s,m),lMs.map{case(l,m)=>(l,mtsub(s,m))})
    case MPoly(m,q) => MPoly(mtsub(s,m),q)
    case MLet(x,q,m1,m2) => MLet(x,tsub(s,q),mtsub(s,m1),mtsub(s,m2))
    case _ => m
  }
  def subEq(s:Map[x,q], eE:List[(q,q)]):List[(q,q)] =
    eE.map{case(t1,t2)=>(tsub(s,t1),tsub(s,t2))}
  def subT(s:Map[x,q], eT:Map[x,q]):Map[x,q] =
    eT.map{case(x,t)=>(x,tsub(s,t))}
  def subK(s:Map[x,q], eK:Map[q,k]):Map[q,k] =
    eK.map{case(q,k)=>(tsub(s,q),ksub(s,k))}

  def ssub(s:Map[x,q], s1:Map[x,q]):Map[x,q] = {
    def xtsub(s:Map[x,q], x:x):x = {
      s.get(x) match {
        case Some(Tx(x)) => xtsub(s,x)
        // todo ssub の xは書き換え対象かよく考える
        case Some(t) => throw new Exception("ssub error")
        case _ => x
      }
    }
    s1.map{case(x,t)=>(xtsub(s,x),tsub(s,t))}
  }

  // Free Type variables
  def ftv(q:q):Set[x] = q match {
    case Tx(x) => Set(x)
    case TArr(q1,q2) => ftv(q1)++ftv(q2)
    case TRecord(f) => f.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case TVariant(f) => f.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case TAll(t,k,q) => kftv(k)++ftv(q) - t
    case _ => Set()
  }
  def kftv(k:k):Set[x] = k match {
    case U => Set()
    case KRecord(f) => f.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case KVariant(f) => f.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
  }
  def eftv(eK:Map[q,k], q:q):Set[x] = {
    eK.get(q) match {
      case None => ftv(q)
      case Some(k) => ftv(q)++kftv(k)
    }
  }

  // Type system
  var i = 0
  def reset() { i = 0 }
  def reset(ii:Int) { i = ii }
  def fresh():x = {
    val I = i
    i += 1
    "x"+I
  }
  def fresht():q = Tx(fresh())

  // Kinded Unification
  def ⊆(f1:List[x], f2:List[x]) = f1.toSet == (f2.toSet & f1.toSet)
  def ±(f1:List[(x,q)], f2:List[(x,q)]):List[(x,q)] = {
    (dom(f1)++dom(f2)).map{l =>
      (f1.toMap.get(l),f2.toMap.get(l)) match {
        case (Some(t1),Some(t2)) => assert(t1 == t2); (l, t1)
        case (Some(t1),None) => (l, t1)
        case (None,Some(t2)) => (l, t2)
        case (None,None) => throw new Exception("assert ±")
      }
    }
  }
  def dom(f:List[(x,q)]):List[x] = f.map{case(l,_)=>l}

  def u(eK:Map[q,k], eE:List[(q,q)]):(Map[q,k],Map[x,q]) = u(eE,eK,Map(),Map())
  def u:((List[(q,q)],Map[q,k],Map[x,q],Map[q,k]))=>(Map[q,k],Map[x,q]) = {
    case (List(),eK,s,sK) => (eK,s)
    case ((t1,t2)::eE,eK,s,sK) =>
      u(try { u1((t1,t2)::eE,eK,s,sK) } catch { case _:Throwable => u1((t2,t1)::eE,eK,s,sK) })
  }
  def u1:(List[(q,q)],Map[q,k],Map[x,q],Map[q,k])=>(List[(q,q)],Map[q,k],Map[x,q],Map[q,k]) = {
    // case (eE,eK,s,sK) if {println("a:u1"+(eE,eK,s,sK)); false} => throw new Exception("assert")
    // (i) type
    case((t1,t2)::eE,eK,s,sK) if t1==t2 => (eE,eK,s,sK)
    // (ii)
    case((t@Tx(x),t2)::eE,eK,s,sK) if !ftv(t2).contains(x) && eK.get(t)==Some(U) =>
      (subEq(Map(x->t2),eE),        subK(Map(x->t2),eK-t),
       ssub(Map(x->t2),s)+(x->t2), subK(Map(x->t2),sK)+(t->U))
    case((t@Tx(x),t2)::eE,eK,s,sK) if !ftv(t2).contains(x) && !eK.contains(t) =>
      u1((t,t2)::eE,eK+(t->U),s,sK)
    case((TAll(t,eK,t1),t2)::eE,eK0,s,sK) => u1((t1,t2)::eE,eK0+(Tx(t)->eK),s,sK)
    // (iii) record
    case ((t1@Tx(x1),t2@Tx(x2))::eE,eK0,s,sK) if ((eK0.get(t1),eK0.get(t2))match{case (Some(KRecord(f1)),Some(KRecord(f2)))=>true case (_,_) =>false})=>
      val (KRecord(f1),KRecord(f2)) = (eK0(t1),eK0(t2))
      (subEq(Map(x1->t2),eE:::(dom(f1).toSet&dom(f2).toSet).toList.map{(l:x)=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
        subK(Map(x1->t2),eK0-t1-t2)+(t2->ksub(Map(x1->t2),KRecord(±(f1, f2)))),
        ssub(Map(x1->t2),s)+(x1->t2),
        subK(Map(x1->t2),sK)+(t1->KRecord(f1)))
    // (iv) record2
    case((t1@Tx(x1),t2@TRecord(f2))::eE,eK0,s,sK) if (eK0.get(t1)match{case Some(KRecord(f1))=> ⊆(dom(f1),dom(f2)) && !ftv(t2).contains(x1) case _ =>false}) =>
      val KRecord(f1) = eK0(t1)
      (subEq(Map(x1->t2),eE:::dom(f1).map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
        subK(Map(x1->t2),eK0-t1),
        ssub(Map(x1->t2),s)+(x1->t2),
        subK(Map(x1->t2),sK)+(t1->KRecord(f1)))
    // (v) record3
    case((TRecord(f1),TRecord(f2))::eE,eK,s,sK) if dom(f1)==dom(f2) =>
      (eE:::dom(f1).map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))},eK,s,sK)
    // (vi) variant
    case((t1@Tx(x1),t2@Tx(x2))::eE,eK0,s,sK)
      if (eK0.get(t1),eK0.get(t2))==(Some(KVariant(_)),Some(KVariant(_))) =>
      val (KVariant(f1),KVariant(f2)) = (eK0(t1),eK0(t2))
      (subEq(Map(x1->t2),eE:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
        subK(Map(x1->t2),eK0-t1-t2)+(t2->ksub(Map(x1->t2),KVariant(±(f1,f2)))),
        ssub(Map(x1->t2),s)+(x1->t2),
        subK(Map(x1->t2),sK)+(t1->KVariant(f1)))
    // (vii) variant2
    case((t1@Tx(x1),t2@TVariant(f2))::eE,eK0,s,sK)
      if (eK0.get(t1)match{case Some(KVariant(f1))=> ⊆(dom(f1),dom(f2)) && !ftv(t2).contains(x1) case _ => false}) =>
      val KVariant(f1) = eK0(t1)
      (subEq(Map(x1->t2),eE:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
        subK(Map(x1->t2),eK0-t1),
        ssub(Map(x1->t2),s)+(x1->t2),
        subK(Map(x1->t2),sK)+(t1->KVariant(f1)))
    // (viii) variant3
    case((t1@TVariant(f1),t2@TVariant(f2))::eE,eK,s,sK) =>
      (eE:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))},eK,s,sK)
    // (ix) arr
    case((TArr(t11,t21),TArr(t12,t22))::eE,eK,s,sK) =>
      (eE:::List((t11,t12),(t21,t22)),eK,s,sK)
  }

  // alorighm WK
  def cls(eK:Map[q,k], eT:Map[x,q], t:q):(Map[q,k],q) = t match {
    case TAll(x,k,t) => (eK,TAll(x,k,t))
    case t =>
      val ts = eftv(eK, t).toSet - eftv(eK, TRecord(eT.toList)).toSet
      val eK1 = eK.filter{case(Tx(x),_)=>ts.contains(x) case(_,_)=>false}
      (eK -- eK1.keys,eK1.foldRight(t){case ((Tx(x),k),t) => TAll(x,k,t)})
  }

  def wk(eK:Map[q,k], eT:Map[x,q], e:mss.e):(Map[q,k],Map[x,q],m,q) = e match {
    case mss.EInt(i) => (eK,Map(),MInt(i),TInt)
    case mss.ETrue => (eK,Map(),MTrue,TBool)
    case mss.EFalse => (eK,Map(),MFalse,TBool)
    case mss.Ex(x) =>
      def foldxq(q:q, eK:Map[q,k], s:Map[x,q]):(List[q],q,Map[q,k],Map[x,q]) = q match {
        case TAll(t_,k,q) =>
          val ti = fresht()
          val (ts,q_,eK_,s_) = foldxq(q,eK,s)
          (ti::ts,q_,eK_ +(ti->k),s_ +(t_ -> ti))
        case q => (List(),q,eK,s)
      }
      val (ts,t,eK_,s)=foldxq(eT(x),Map(),Map())
      (eK ++ eK_.map{case(ti,ki)=>(ti,ksub(s,ki))},Map(),if (ts==List()) Mx(x) else MTApp(Mx(x),ts),tsub(s,t))
    case mss.EAbs(x,e1) =>
      val t = fresht()
      val (eK1,s1,m1,t1) = wk(eK+(t->U),eT+(x->t),e1)
      val t_ = tsub(s1,t)
      (eK1,s1,MAbs(x,t_,m1),TArr(t_,t1))
    case mss.EApp(e1,e2) =>
      val (eK1,s1,m1,q1) = wk(eK,eT,e1)
      val (eK2,s2,m2,q2) = wk(eK1,subT(s1,eT),e2)
      val t = fresht()
      val (eK3,s3) = u(eK2,List(tsub(s2,q1)->TArr(q2,t)))
      val s32 = s3++s2
      (eK3,s32++s1,MApp(mtsub(s32,m1), mtsub(s3,m2)),tsub(s3,t))
    case mss.ERecord(les) =>
      val (_,kn,sn,lms,lts) = les.foldLeft((eT,eK,Map[x,q](),List[(l,m)](),List[(l,q)]())) {
        case ((eT,eK,s,lms,lqs),(l1,e1)) =>
          val (eK1,s1,m1,t1) = wk(eK,eT,e1)
          (subT(s1,eT),eK1,s1++s,(l1->m1)::lms,(l1->t1)::lqs)
      }
      (kn,sn,MRecord(lms.reverse),TRecord(lts.reverse))
    case mss.EDot(e1,l) =>
      val (eK1,s1,m1,t0) = wk(eK,eT,e1)
      val t1 = fresht()
      val t2 = fresht()
      val (eK2,s2) = u(eK1+(t1->U)+(t2->KRecord(List(l->t1))),List((t2,t0)))
      val s = s2++s1
      (eK2,s,MDot(mtsub(s,m1),tsub(s,t2), l),tsub(s,t1))
    case mss.EModify(e1,l,e2) =>
      val (eK1,s1,m1,t1) = wk(eK,eT,e1)
      val (eK2,s2,m2,t2) = wk(eK1,subT(s1,eT),e2)
      val (t1_,t3,t4) = (tsub(s2,t1), fresht(), fresht())
      val (eK3,s3) = u(eK2++Map(t3->U,t4->KRecord(List(l->t3))),List((t3,t2),(t4,t1_)))
      val s32 = s3++s2
      val t4_ = tsub(s3,t4)
      (eK3,s32++s1,MModify(mtsub(s32,m1),t4_,l,mtsub(s3,m2)),t4_)
    case mss.ECase(e0,les) =>
      val (eK0,s0,m0,q0) = wk(eK,eT,e0)
      val t0 = fresht()
      val (eKn,_,lms,lts,eKn_,tts,s) = les.foldRight(
        (eK0,subT(s0,eT),List[(x,m)](),List[(x,q)](),Map[q,k](),List[(q,q)](),s0)
      ) { case ((li,ei),(eKi1,eTi1,ms1,lts1,eK1,tts1,s1))=>
        val (eKi,si,mi,qi) = wk(eKi1,eTi1,ei)
        val ti = fresht()
        (eKi,subT(si++s1,eTi1),(li,mi)::ms1,(li->ti)::lts1,eK1+(ti->U),(qi,TArr(ti,t0))::tts1,si++s1)
      }
      val (eKn1,sn1) = u(eKn++eKn_,(tsub(s--s0.keys,q0),TVariant(lts))::tts.map{ case (qi,ti) => (tsub(s,qi),ti) })
      (eKn1,sn1++s, MCase(mtsub(sn1++s,m0),lms.map{case(li,mi)=>(li,mtsub(s,mi))}),tsub(sn1,t0))
    case mss.EVariant(l,e1) =>
      val (eK1,s1,m1,τ1) = wk(eK,eT,e1)
      val t = fresht()
      (eK1+(t->KVariant(List(l->τ1))),s1,MVariant(l,m1,t),t)
    case mss.ELet(x,e1,e2) =>
      val (eK1,s1,m1,t1) = wk(eK,eT,e1)
      val eT1 = subT(s1,eT)
      val (k1_,q1) = cls(eK1,eT1,t1)
      val (eK2,s2,m2,t2) = wk(k1_,eT1+(x->q1),e2)
      val q1_ = tsub(s2,q1)
      (eK2,s2++s1,MLet(x,q1_,MPoly(mtsub(s2,m1),q1_),m2),t2)
  }
}
