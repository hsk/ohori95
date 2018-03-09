package mss2
// ML-Style System λlet,#
object mss2 {

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

  trait E
  case object ETrue extends E
  case object EFalse extends E
  case class EInt(v:Int) extends E
  case class Ex(v:String) extends E
  case class EAbs(x:String,E:E) extends E
  case class EApp(M1:E,M2:E) extends E
  case class ERecord(v:List[(l,E)]) extends E
  case class EDot(E:E,l:l) extends E
  case class EModify(E:E,l:l,E2:E) extends E
  case class EVariant(l:l,E:E) extends E
  case class ECase(E:E,w:List[(l,E)]) extends E
  case class ELet(x:x,e1:E,e2:E) extends E
  def v(e:E):Boolean = e match {
    case e if cb(e) => true
    case EAbs(x,_) => true
    case ERecord(les) => !les.exists{case(l,e)=> !v(e)}
    case EVariant(l,e) => v(e)
    case _ => false
  }
  def i(e:E)   = e match {case EInt(_) => true case _ => false}
  def cb(e:E)  = e match {case ETrue => true case EFalse => true case _ => i(e)}
  def x(e:E)   = e match {case Ex(_)=>true case _=>false}
  def e(e:Any) = e match {case _:E=>true case _=>false}

  trait M
  case class Mx(x:x) extends M
  case class MTApp(M1:M,σ:σ) extends M
  case object MTrue extends M
  case object MFalse extends M
  case class MInt(i:Int) extends M
  case class MAbs(x:x,σ:σ,M:M) extends M
  case class MApp(M1:M,M2:M) extends M
  case class MRecord(v:List[(l,M)]) extends M
  case class MDot(M:M,σ:σ,l:l) extends M
  case class MModify(M:M,σ:σ,l:l,M2:M) extends M
  case class MVariant(l:l,M:M,σ:σ) extends M
  case class MCase(M:M,w:List[(l,M)]) extends M
  case class MPoly(M:M,σ:σ) extends M
  case class MLet(x:x,σ:σ,M1:M,M2:M) extends M
  def M(M:Any) = M match {case _:M=>true case _=>false}
  def mi(m:M)   = m match {case MInt(_) => true case _ => false}
  def mcb(m:M)  = m match {case MTrue => true case MFalse => true case _ => mi(m)}

  // Reduction rules
  def evHole(e:E):(E,E=>E) = e match {
    case EApp(e1,e2) if !v(e1) =>
      evHole(e1) match {case(e,h)=>(e,{e=>EApp(h(e),e2)})}
    case EApp(v1,e2) if !v(e2) =>
      evHole(e2) match {case(e,h)=>(e,{e=>EApp(v1,h(e))})}
    case ELet(x,e1,e2) if !v(e1) =>
      evHole(e1) match {case(e,h)=>(e,{e=>ELet(x,h(e),e2)})}
    case ERecord(les) =>
      def find(hs:List[(l,E)],ls:List[(l,E)]):(E,E=>E) = ls match {
        case List() => (e,{e=>e})
        case (l,e)::ls if !v(e) => (e,{e=>ERecord(hs.reverse:::(l,e)::ls)})
        case (l,e)::ls => find((l,e)::hs,ls)
      }
      find(List(),les)
    case EDot(e,l) =>
      evHole(e) match{case(e,h)=>(e,{e=>EDot(h(e),l)})}
    case EModify(e1,l,e2) if !v(e1) =>
      evHole(e1) match{case(e,h)=>(e,{e=>EModify(h(e),l,e2)})}
    case EModify(v1,l,e2) if !v(e2) =>
      evHole(e2) match{case(e,h)=>(e,{e=>EModify(v1,l,h(e))})}
    case EVariant(l,e) if !v(e) =>
      evHole(e) match{case(e,h)=>(e,{e=>EVariant(l,h(e))})}
    case ECase(e,lEs) if !v(e) =>
      evHole(e) match{case(e,h)=>(e,{e=>ECase(h(e),lEs)})}
    case e => (e,{e=>e})
  }
  def ev1(e:E):E = {
    e match {
    case EApp(EAbs(x,e),v1) if v(v1) => esub(Map(x->v1),e)
    case EDot(ERecord(lvs),li) => lvs.toMap.apply(li)
    case EModify(ERecord(lvs),li,v) =>
      def find(hs:List[(l,E)],ls:List[(l,E)]):E = ls match {
        case List() => ERecord(hs.reverse)
        case (l,e)::ls if l==li => ERecord(hs.reverse:::(l,v)::ls)
        case (l,e)::ls => find((l,e)::hs,ls)
      }
      find(List(),lvs)
    case ECase(EVariant(li,v),ls) => EApp(ls.toMap.apply(li),v)
    case ELet(x,v,e) => esub(Map(x->v),e)
    case e => throw new Exception("error")
    }
  }
  def eval1(e:E):E = try {
    val (e1,f)=evHole(e)
    f(ev1(e1))
  } catch {
    case _:Throwable => ev1(e)
  }
  def eval(e:E):E = try {
    eval(eval1(e))
  } catch {
    case _:Throwable => e
  }

  // Substitutions

  def esub(S:Map[x,E],e:E):E = e match {
    case Ex(x) if S.contains(x) => esub(S,S(x))
    case Ex(x) => Ex(x)
    case e if cb(e) => e
    case EAbs(x,e) => EAbs(x,esub(S - x,e))
    case EApp(e1,e2) => EApp(esub(S,e1),esub(S,e2))
    case ERecord(les) => ERecord(les.map{case(l,e)=>(l,esub(S,e))})
    case EDot(e,l) => EDot(esub(S,e),l)
    case EModify(e1,l,e2) => EModify(esub(S,e1),l,esub(S,e2))
    case EVariant(l,e) => EVariant(l,esub(S,e))
    case ECase(e,les) => ECase(esub(S,e),les.map{case(l,e)=>(l,esub(S,e))})
    case ELet(x,e1,e2) => ELet(x,esub(S,e1),esub(S,e2))
  }
  def tsub(S:Map[x,σ],σ:σ):σ = σ match {
    case tx(x) if S.contains(x) => tsub(S,S(x))
    case tx(x) => tx(x)
    case _ if b(σ) => σ
    case tarr(σ1,σ2) => tarr(tsub(S,σ1),tsub(S,σ2))
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
    case MTApp(m,σ) => MTApp(msub(S,m),σ)
    case m if mcb(m) => m
    case MAbs(x,σ,m) => MAbs(x,σ,msub(S - x,m))
    case MApp(m1,m2) => MApp(msub(S,m1),msub(S,m2))
    case MRecord(lms) => MRecord(lms.map{case(l,m)=>(l,msub(S,m))})
    case MDot(m,σ,l) => MDot(msub(S,m),σ,l)
    case MModify(m1,σ,l,m2) => MModify(msub(S,m1),σ,l,msub(S,m2))
    case MVariant(l,m,σ) => MVariant(l,msub(S,m),σ)
    case MCase(m,lMs) => MCase(msub(S,m),lMs.map{case(l,m)=>(l,msub(S,m))})
    case MPoly(m,σ) => MPoly(msub(S,m),σ)
    case MLet(x,σ,m1,m2) => MLet(x,σ,msub(S,m1),msub(S-x,m2))
  }
  def mtsub(S:Map[x,σ],M:M):M = M match {
    case MTApp(m,σ) => MTApp(mtsub(S,m),tsub(S,σ))
    case MAbs(x,σ,m) => MAbs(x,tsub(S,σ),mtsub(S,m))
    case MApp(m1,m2) => MApp(mtsub(S,m1),mtsub(S,m2))
    case MRecord(lMs) => MRecord(lMs.map{case(l,m)=>(l,mtsub(S,m))})
    case MDot(m,σ,l) => MDot(mtsub(S,m),tsub(S,σ),l)
    case MModify(m1,σ,l,m2) => MModify(mtsub(S,m1),tsub(S,σ),l,mtsub(S,m2))
    case MVariant(l,m,σ) => MVariant(l,mtsub(S,m),tsub(S,σ))
    case MCase(m,lMs) => MCase(mtsub(S,m),lMs.map{case(l,m)=>(l,mtsub(S,m))})
    case MPoly(m,σ) => MPoly(mtsub(S,m),σ)
    case MLet(x,σ,m1,m2) => MLet(x,tsub(S,σ),mtsub(S,m1),mtsub(S,m2))
    case _ => M
  }
  def subEq(S:Map[x,σ],eq:List[(σ,σ)]):List[(σ,σ)] =
    eq.map{case(t1,t2)=>(tsub(S,t1),tsub(S,t2))}
  def subT(S:Map[x,σ],T:Map[x,σ]):Map[x,σ] =
    T.map{case(x,t)=>(x,tsub(S,t))}
  def subK(S:Map[x,σ],K:Map[σ,k]):Map[σ,k] =
    K.map{case(σ,k)=>(tsub(S,σ),ksub(S,k))}

  def ssub(S:Map[x,σ],S1:Map[x,σ]):Map[x,σ] = {
    def xtsub(S:Map[x,σ],x:x):x = {
      S.get(x) match {
        case Some(tx(x)) => xtsub(S,x)
        // todo ssub の xは書き換え対象かよく考える
        case Some(t) => throw new Exception("ssub error")
        case _ => x
      }
    }
    S1.map{case(x,t)=>(xtsub(S,x),tsub(S,t))}
  }

  // Free Type variables
  def ftv(σ:σ):Set[x] = σ match {
    case tx(x) => Set(x)
    case _ if b(σ) => Set()
    case tarr(σ1,σ2) => ftv(σ1)++ftv(σ2)
    case trecord(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case tvariant(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case ∀(t,k,σ) => kftv(k)++ftv(σ) - t
  }
  def kftv(k:k):Set[x] = k match {
    case U => Set()
    case krecord(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
    case kvariant(lMs) => lMs.foldLeft(Set[x]()){case(tv,(_,m))=>tv++ftv(m)}
  }
  def tftv(T:Map[x,σ]):Set[x] =
    T.foldLeft(Set[x]()){case(tv,(_,σ))=>tv++ftv(σ)}
  def eftv(K:Map[σ,k],σ:σ):Set[x] = {
    val FTV = ftv(σ)
    K.get(σ) match {
      case None => FTV
      case Some(k) => FTV++kftv(k)
    }
  }

  // Type system
  var i = 0
  def reset() { i = 0 }
  def fresh():x = {
    val I = i
    i += 1
    "x"+I
  }
  def fresht():σ = tx(fresh())

  // 3.4 Kinded Unification
  def ⊆(F1:List[x], F2:List[x]) = F1.toSet == (F2.toSet & F1.toSet)
  def ±(F1:List[(x,σ)], F2:List[(x,σ)]):List[(x,σ)] = {
    (dom(F1)++dom(F2)).map{l=>
      val t1 = F1.toMap.apply(l)
      val t2 = F2.toMap.apply(l)
      assert(t1==t2)
      (l,t1)
    }
  }
  def dom(F:List[(x,σ)]):List[x] = F.map{case(l,_)=>l}

  def u(K:Map[σ,k],E:List[(σ,σ)]):(Map[σ,k],Map[x,σ]) = {
    val (_,k0,s,_) = u(E,K,Map(),Map())
    (k0,s)
  }
  def u(E:List[(σ,σ)],K:Map[σ,k],S:Map[x,σ],sk:Map[σ,k]):(List[(σ,σ)],Map[σ,k],Map[x,σ],Map[σ,k]) = E match {
    case List() => (List(),K,S,sk) // writeln(b:u([],K,S,sk))
    case (t1,t2)::e =>
      val (e1,k1,s1,sK1) = try {
         u1((t1,t2)::e,K,S,sk)
      } catch {
        case _:Throwable => u1((t2,t1)::e,K,S,sk)
      }
      u(e1,k1,s1,sK1)
  }
  def u1:(List[(σ,σ)],Map[σ,k],Map[x,σ],Map[σ,k])=>(List[(σ,σ)],Map[σ,k],Map[x,σ],Map[σ,k]) = {
    // case (e,k,s,sk) if {println("a:u1"+(e,k,s,sk)); false} => throw new Exception("assert")
    // (i) type
    case((τ1,τ2)::e,k,s,sk) if τ1==τ2 => (e,k,s,sk)
    // (ii)
    case((t@tx(x),τ)::e,k,s,sk) if !ftv(τ).contains(x) && k.get(t)==Some(U) =>
      (subEq(Map(x->τ),e),       subK(Map(x->τ),k-t),
       ssub(Map(x->τ),s)+(x->τ), subK(Map(x->τ),sk)+(t->U))
    case((t@tx(x),τ)::e,k,s,sk) if !ftv(τ).contains(x) && !k.contains(t) =>
      u1((t,τ)::e,k+(t->U),s,sk)
    case((∀(t,k,t1),τ)::e,k0,s,sk) => u1((t1,τ)::e,k0+(tx(t)->k),s,sk)
    // (iii) record
    case ((t1@tx(x1),t2@tx(x2))::e,k0,s,sk) if ((k0.get(t1),k0.get(t2))match{case (Some(krecord(f1)),Some(krecord(f2)))=>true case (_,_) =>false})=>
      val (krecord(f1),krecord(f2)) = (k0(t1),k0(t2))
      (subEq(Map(x1->t2),e:::(dom(f1).toSet&dom(f2).toSet).toList.map{(l:x)=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
       subK(Map(x1->t2),k0-t1-t2)+(t2->ksub(Map(x1->t2),krecord(±(f1, f2)))),
       ssub(Map(x1->t2),s)+(x1->t2),
       subK(Map(x1->t2),sk)+(t1->krecord(f1)))
    // (iv) record2
    case((t1@tx(x1),t2@trecord(f2))::e,k0,s,sk) if (k0.get(t1)match{case Some(krecord(f1))=> ⊆(dom(f1),dom(f2)) && !ftv(t2).contains(x1) case _ =>false}) =>
      val krecord(f1) = k0(t1)
      (subEq(Map(x1->t2),e:::dom(f1).map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
       subK(Map(x1->t2),k0-t1),
       ssub(Map(x1->t2),s)+(x1->t2),
       subK(Map(x1->t2),sk)+(t1->krecord(f1)))
    // (v) record3
    case((trecord(f1),trecord(f2))::e,k,s,sk) if dom(f1)==dom(f2) =>
      (e:::dom(f1).map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))},k,s,sk)
    // (vi) variant
    case((t1@tx(x1),t2@tx(x2))::e,k0,s,sk)
      if ((k0.get(t1),k0.get(t2))match{case (Some(kvariant(f1)),Some(kvariant(f2)))=>true case (_,_) => false}) =>
      val (kvariant(f1),kvariant(f2)) = (k0(t1),k0(t2))
      (subEq(Map(x1->t2),e:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
       subK(Map(x1->t2),k0-t1-t2)+(t2->ksub(Map(x1->t2),kvariant(±(f1,f2)))),
       ssub(Map(x1->t2),s)+(x1->t2),
       subK(Map(x1->t2),sk)+(t1->kvariant(f1)))
    // (vii) variant2
    case((t1@tx(x1),t2@tvariant(f2))::e,k0,s,sk)
      if (k0.get(t1)match{case Some(kvariant(f1))=> ⊆(dom(f1),dom(f2)) && !ftv(t2).contains(x1) case _ => false}) =>
      val kvariant(f1) = k0(t1)
      (subEq(Map(x1->t2),e:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))}),
       subK(Map(x1->t2),k0-t1),
       ssub(Map(x1->t2),s)+(x1->t2),
       subK(Map(x1->t2),sk)+(t1->kvariant(f1)))
    // (viii) variant3
    case((t1@tvariant(f1),t2@tvariant(f2))::e,k,s,sk) =>
      (e:::(dom(f1).toSet & dom(f2).toSet).toList.map{l=>(f1.toMap.apply(l),f2.toMap.apply(l))},k,s,sk)
    // (ix) arr
    case((tarr(τ11,τ21),tarr(τ12,τ22))::e,k,s,sk) =>
      (e:::List((τ11,τ12),(τ21,τ22)),k,s,sk)
  }

  // alorighm WK
  def cls(K:Map[σ,k],T:Map[x,σ],τ:σ):(Map[σ,k],σ) = τ match {
    case ∀(t,k,τ) => (K,∀(t,k,τ))
    case τ =>
      val ts = eftv(K, τ).toSet - eftv(K, trecord(T.toList)).toSet
      val k1 = K.filter{case(tx(ti),_)=>ts.contains(ti) case(_,_)=>false}
      (K -- k1.keys,k1.foldRight(τ){case ((tx(ti),ki),τi) => ∀(ti,ki,τi)})
  }

  def wk(K:Map[σ,k],T:Map[x,σ],e:E):(Map[σ,k],Map[x,σ],M,σ) = {
    // println("e="+e)
    e match {
    case EInt(i) => (K,Map(),MInt(i),tint)
    case ETrue => (K,Map(),MTrue,tbool)
    case EFalse => (K,Map(),MFalse,tbool)
    case Ex(x) =>
      def foldxq(x:M,q:σ,Ks:Map[σ,k],S:Map[x,σ]):(M,σ,Map[σ,k],Map[x,σ]) = q match {
          case ∀(t_,k,q) =>
            val Si = fresht()
            val (x_,q_,ks_,s_) = foldxq(MTApp(x,Si),q,Ks,S)
            (x_,q_,ks_ +(Si->k),s_ +(t_ -> Si))
          case q => (x,q,Ks,S)
        }
      val (x_,sτ1,sKs,s)=foldxq(Mx(x),T(x),Map(),Map())
      val sKs_ = sKs.map{case(si,ki)=>(si,ksub(s,ki))}
      (K ++ sKs_,Map(),x_,tsub(s,sτ1))
    case EAbs(x,e1) =>
      val t = fresht()
      val (k1,s1,m1,t1) = wk(K+(t->U),T+(x->t),e1)
      val t_ = tsub(s1,t)
      (k1,s1,MAbs(x,t_,m1),tarr(t_,t1))
    case EApp(e1,e2) =>
      val (k1,s1,m1,σ1) = wk(K,T,e1)
      val (k2,s2,m2,σ2) = wk(k1,subT(s1,T),e2)
      val t = fresht()
      val (k3,s3) = u(k2,List(tsub(s2,σ1)->tarr(σ2,t)))
      val s32 = s3++s2
      (k3,s32++s1,MApp(mtsub(s32,m1), mtsub(s3,m2)),tsub(s3,t))
    case ERecord(List()) => (K,Map(),MRecord(List()),trecord(List()))
    case ERecord((l1,e1)::les) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val (kn,s,MRecord(lMs),trecord(lTs)) = wk(k1,subT(s1,T),ERecord(les))
      (kn,s1++s,MRecord((l1->m1)::lMs),trecord((l1->τ1)::lTs))
    case EDot(e1,l) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val t1 = fresht()
      val t2 = fresht()
      val (k2,s2) = u(k1+(t1->U)+(t2->krecord(List(l->t1))),List((t2,τ1)))
      val s = s2++s1
      (k2,s,MDot(mtsub(s,m1),tsub(s,t2), l),tsub(s,t1))
    case EModify(e1,l,e2) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val (k2,s2,m2,τ2) = wk(k1,subT(s1,T),e2)
      val (τ1_,t1,t2) = (tsub(s2,τ1), fresht(), fresht())
      val (k3,s3) = u(k2++Map(t1->U,t2->krecord(List(l->t1))),List((t1,τ2),(t2,τ1_)))
      val s32 = s3++s2
      val t2_ = tsub(s3,t2)
      (k3,s32++s1,MModify(mtsub(s32,m1),t2_,l,mtsub(s3,m2)),t2_)
    case ECase(e0,les) =>
      val (k0,s0,m0,τ0) = wk(K,T,e0)
      val (kn,_,lms,lts,kn_,tts,s) = les.foldRight(
        (k0,subT(s0,T),List[(x,M)](),List[(x,σ)](),Map[σ,k](),List[(σ,σ)](),Map[x,σ]())
      ){
        case ((li,ei),(ki1,ti1,ms1,lts1,k1,tts1,s1))=>
        val (ki,si,mi,τi) = wk(ki1,ti1,ei)
        val ti = fresht()
        (ki,subT(si++s1,ti1),(li,mi)::ms1,(li->ti)::lts1,k1+(ti->U),(τi,ti)::tts1,si++s1)
      }
      val t0 = fresht()
      val tts_ = tts.map{case(τi,ti)=>(tsub(s,τi),(tarr(t0,ti)))}
      val (kn1,sn1) = u(kn++kn_,(tsub(s,τ0),tvariant(lts))::tts_)
      val s_ = sn1++s
      (kn1,s_, MCase(mtsub(s_,m0),lms.map{case(li,mi)=>(li,mtsub(s,mi))}),tsub(sn1,t0))
    /*
    WK(K,T,case e0 of <l1=e1,···,ln=en>) =
      let (K0,S0,M0,τ0) = WK(K,T,e0)
          (Ki,Si,Mi,τi) = WK(Ki−1,Si−1◦···◦S0(T),ei) (1 ≤ i ≤ n)
          (Kn+1,Sn+1) =U(Kn{t0::U,···,tn::U},{(Sn◦···S1(τ0),<l1:t1,···,ln:tn>)}
                        ∪{(Sn◦···Si+1(τi),ti→t0)|1 ≤ i ≤ n}) (t0,···,tn fresh)
      in (Kn+1,Sn+1◦···◦S0,
          (case Sn+1◦···◦S1(M0) of <···,li=Sn+1◦···◦Si+1(Mi),···>),Sn+1(t0))
    WK(K,T,<l=e1>) = let (K1,S1,M1,τ1) = WK(K,T,e1)
                     in (K1{t::<<l:τ1>>},S1,(<l=M1>:t),t) (t fresh)
    */
    case EVariant(l,e1) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val t = fresht()
      (k1+(t->kvariant(List(l->τ1))),s1,MVariant(l,m1,t),t)
    case ELet(x,e1,e2) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val t1 = subT(s1,T)
      val (k1_,σ1) = cls(k1,t1,τ1)
      val (k2,s2,m2,τ2) = wk(k1_,t1+(x->σ1),e2)
      val σ1_ = tsub(s2,σ1)
      (k2,s2++s1,MLet(x,σ1_,MPoly(mtsub(s2,m1),σ1_),m2),τ2)
    }
  }
}
