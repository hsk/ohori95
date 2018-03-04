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

  /*
  e ::= x | cb | λ(x,e) | (e $ e) | (let(x=e);e)
      | record(l=e) | e#l | modify(e,l,e)
      | {[l=e]} | case(e,variant(l=e)).
  */
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

  /*
  'M' ::= x | 'M'!q | cb | λ(x:q,'M') | ('M' $ 'M') | poly('M':q) | (let(x:q = 'M');'M')
      | record(l='M') | ('M':q) # l | modify('M':q,l,'M')
      | ({[l='M']}:q) | case('M',variant(l='M')).
  */
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
  def xtsub(S:Map[x,σ],x:x):x =
    S.get(x) match {
      case Some(tx(x)) => xtsub(S,x)
      case _ => x
    }
  def subEq(S:Map[x,σ],eq:Map[σ,σ]):Map[σ,σ] =
    eq.map{case(t1,t2)=>(tsub(S,t1),tsub(S,t2))}
  def subT(S:Map[x,σ],T:Map[x,σ]):Map[x,σ] =
    T.map{case(x,t)=>(x,tsub(S,t))}
  def ssub(S:Map[x,σ],S1:Map[x,σ]):Map[x,σ] =
    S1.map{case(x,t)=>(xtsub(S,x),tsub(S,t))}
  /*
  // Free Type variables

  ftv(B,[]) :- b(B),!.
  ftv(X,[X]) :- x(X).
  ftv((Q1->Q2),FTV) :- ftv(Q1,FTV1),ftv(Q2,FTV2),union(FTV1,FTV2,FTV).
  ftv(LTs,FTVs) :- foldl([_:T,FTV,FTV_]>>(ftv(T,FTVi),union(FTV,FTVi,FTV_)),LTs,[],FTVs).
  ftv({LTs},{FTVs}) :- foldl([_:T,FTV,FTV_]>>(ftv(T,FTVi),union(FTV,FTVi,FTV_)),LTs,[],FTVs).
  ftv(∀(T,K,Q),FTV) :- kftv(K,KFTV),ftv(Q,QFTV),union(KFTV,QFTV,FTV1),subtract(FTV1,T,FTV).

  kftv(u,[]).
  kftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
  kftv({LQs},FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).
  tftv(LQs,FTVs) :- foldl([_:M,FTV,FTV_]>>(ftv(M,FTVi),union(FTV,FTVi,FTV_)),LQs,[],FTVs).

  eftv(K,σ,EFTV) :- ftv(σ,FTV),member(σ:k,K),kftv(k,FTV2),union(FTV,FTV2,EFTV).
  eftv(_,σ,FTV) :- ftv(σ,FTV).
*/
  // Type system
  var i = 0
  def reset() { i = 0 }
  def fresh():x = {
    val I = i
    i += 1
    "%x"+I
  }
  def fresht():σ = tx(fresh())

  // 3.4 Kinded Unification
/*
  F1 ⊆ F2 :- intersection(F2,F1,F1_),length(F1,L),length(F1_,L).
  ±(F1, F2, F) :-
    dom(F1,Dom1),dom(F2,Dom2),union(Dom1,Dom2,Dom),
    maplist([L,t]>>(member(L:t,F1);member(L:t,F2)),Dom,F).

  dom(F,Dom) :- maplist([L:_,L]>>!,F,Dom).

  def u:(K:Map[x,k],E:E):(Map[x,k],Map[x,t]) = {
    val (_,K0,S,_) = u(E,K,Map(),Map())
    (K0,S)
  }

  u([],K,S,SK,([],K,S,SK)) /*:- writeln(b:u([],K,S,SK))*/.
  u(E,K,S,SK,(E_,K_,S_,SK_)) :-
    u((E,K,S,SK) ⟹ (E1,K1,S1,SK1)),!,
    u(E1,K1,S1,SK1,(E_,K_,S_,SK_)).
  u([(T1,T2)|E],K,S,SK,(E_,K_,S_,SK_)) :-
    u(([(T2,T1)|E],K,S,SK) ⟹ (E1,K1,S1,SK1)),!,
    u(E1,K1,S1,SK1,(E_,K_,S_,SK_)).

  %u((E,K,S,SK) ⟹ _) :- writeln(a:u(E,K,S,SK)),fail.
  // (i) type
  u(([(τ,τ)|E],K,S,SK) ⟹ (E,K,S,SK)).
  // (ii) 
  u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
    t(t), ftv(τ,FTV), \+member(t,FTV),
    member(t:u,K0), subtract(K0,[t:u],K),!,
    subEq([τ/t],E,E_), ksub([τ/t],K,K_),
    ssub([τ/t],S,S1), union(S1,[τ/t],S_),
    ssub([τ/t],SK,SK1), union(SK1,[u/t],SK_).
  u(([(t,τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
    t(t), ftv(τ,FTV), \+member(t,FTV), \+member(t:_,K0),
    u(([(t,τ)|E],[t:u|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
  u(([(∀(t,k,t1),τ)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
    u(([(t1,τ)|E],[t:k|K0],S,SK) ⟹ (E_,K_,S_,SK_)).
  // (iii) record
  u(([(t1,t2)|E],K0,S,SK) ⟹ (E_, K_, S_,SK_)) :-
    t(t1),t(t2),
    member(t1:F1,K0), record(l:q,F1), member((t2,F2),K0), record(l:q,F2), subtract(K0,[(t1,F1),(t2,F2)],K),
    dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
    maplist({F1,F2}/[l,(Ft1,Ft2)]>>(member(l:Ft1,F1),member(l:Ft2,F2)),Dom12,ED),
    union(E,ED,E1), subEq([t2/t1],E1,E_),
    ksub([t2/t1],K,K1),'±'(F1, F2, F12),tsub([t2/t1],F12,F12_),union(K1,[(t2,F12_)],K_),
    ssub([t2/t1],S,S1), union(S1,[t2/t1],S_),
    ssub([t2/t1],SK,SK1), union(SK1,[F1/t1],SK_).
  // (iv) record2
  u(([(t1,F2)|E],K0,S,SK) ⟹ (E_,K_, S_,SK_)) :- record(l:q,F2),
    member(t1:F1,K0), record(l:q,F1), subtract(K0,[t1:F1],K),
    dom(F1,Dom1), dom(F2,Dom2),Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t, FTV),
    maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
    union(E,ED,E1), subEq([F2/t1],E1,E_),
    ksub([F2/t1],K,K_),
    ssub([F2/t1],S,S1), union(S1,[F2/t1],S_),
    ssub([F2/t1],SK,SK1), union(SK1,[F1/t1],SK_).
  // (v) record3
  u(([(F1,F2)|E],K,S,SK) ⟹ (E_,K,S,SK)) :- record(l:q,F1),record(l:q,F2),
    dom(F1,Dom1), dom(F2,Dom2), Dom1=Dom2,
    maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
    union(E,ED,E_).
  // (vi) variant
  u(([(t1,t2)|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :-
    t(t1),t(t2),
    member((t1,{F1}),K0),list(l:q,F1), member((t2,{F2}),K0),list(l:q,F2), subtract(K0,[(t1,{F1}),(t2,{F2})],K),
    dom(F1,Dom1), dom(F2,Dom2), intersection(Dom1,Dom2,Dom12),
    maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom12,ED),
    union(E,ED,E1), subEq([t2/t1],E1,E_),
    ksub([t2/t1],K,K1), ±(F1,F2, F12), tsub([t2/t1],{F12},{F12_}), union(K1,[(t2,{F12_})],K_),
    ssub([t2/t1],S,S1), union(S1,[t2/t1],S_),
    ssub([t2/t1],SK,SK1), union(SK1,[{F1}/t1],SK_).
  // (vii) variant2
  u(([(t1,{F2})|E],K0,S,SK) ⟹ (E_,K_,S_,SK_)) :- t(t1), list(l:q,F2),
    member((t1:{F1}),K0),list(l:q,F1), subtract(K0,[(t1:{F1})],K),
    dom(F1,Dom1), dom(F2,Dom2), Dom1 ⊆ Dom2, ftv(F2,FTV), \+member(t1, FTV),
    maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom1,ED),
    union(E,ED,E1), subEq([{F2}/t1],E1,E_),
    ksub([{F2}/t1],K,K_),
    ssub([{F2}/t1],S,S1), union(S1,[{F2}/t1],S_),
    ssub([{F2}/t1],SK,SK1), union(SK1,[{F1}/t1],SK_).
  // (viii) variant3
  u(([({F1},{F2})|E],K,S,SK) ⟹ (E_,K,S,SK)) :- list(l:q,F1),list(l:q,F2),
    dom(F1,Dom), dom(F2,Dom),
    maplist({F1,F2}/[L,(Ft1,Ft2)]>>(member(L:Ft1,F1),member(L:Ft2,F2)),Dom,ED),
    union(E, ED, E_).
  // (ix) arr
  u(([((τ11->τ21),(τ12->τ22))|E],K,S,SK) ⟹ (E_,K,S,SK)) :-
    union(E,[(τ11,τ12),(τ21,τ22)],E_).

  // alorighm WK

  foldxq((X,∀(T_,K,Q),Ks,S),(X_,Q_,[Si:K|Ks_],[Si/T_|S_])) :-
    fresh(Si),!,foldxq(((X!Si),Q,Ks,S),(X_,Q_,Ks_,S_)).
  foldxq((X,Q,Ks,S),(X,Q,Ks,S)).

  cls(K, _, ∀(t,k,τ), (K,∀(t,k,τ))).
  cls(K, T, τ, (K0,τ_)) :-
    eftv(K, τ,τFTV), eftv(K, T, TFTV), subtract(τFTV, TFTV, ts),
    findall((Ti:Ki),(member(Ti:Ki,K),member(Ti,ts)),K1),
    subtract(K,K1,K0),foldr([Ti:Ki,τi,∀(Ti,Ki,τi)]>>!,K1,τ,τ_).
  */
  def wk(K:Map[x,k],T:Map[x,σ],e:E):(Map[x,k],Map[x,M],M,σ) = e match {
    case EInt(i) => (K,Map(),MInt(i),tint)
    case ETrue => (K,Map(),MTrue,tbool)
    case EFalse => (K,Map(),MFalse,tbool)
    /*
    case Ex(x) =>
      val (x_,sτ1,SKs,S)=foldxq((x,T(x),[],[]))
      val SKs_ = SKs.map{(Si,Ki)=>(Si,ksub(S,Ki))}
      (K ++ SKs_,Map(),x_,tsub(S,sτ1))
    case EAbs(x,e1) =>    
      val t = fresht()
      val (K1,S1,M1,t1) = wk(K+(t->U),T+(x->t),e1)
      val t_ = tsub(S1,t)
      (K1,S1,MAbs(x,t_,M1),tarr(t_,t1))
    case EApp(e1,e2) =>
      val (K1,S1,M1,σ1) = wk(K,T,E1)
      val (K2,S2,M2,σ2) = wk(K1,subT(S1,T),E2)
      val t = fresht()
      val (K3,S3) = u(K2,List(tsub(S2,σ1)->tarr(σ2,t)))
      val S32 = S3++S2
      (K3,S32++S1,MApp(mtsub(S32,M1), mtsub(S3,M2)),tsub(S3,t))
    */
    case ERecord(List()) => (K,Map(),MRecord(List()),trecord(List()))
    /*
    case ERecord((l1,e1)::les) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val (kn,s,MRecord(lMs),trecord(lTs)) = wk(k1,subT(s1,T),les)
      (kn,s1++s,MRecord((l1->m1)::lMs),trecord((l1->τ1)::lTs))
    case EDot(e1,l) =>
      val (K1,S1,M1,τ1) = wk(K,T,e1)
      val t1 = fresht()
      val t2 = fresht()
      val (K2,S2) = u([t1:u,t2:[l:t1]|K1],[(t2,τ1)])
      val S = S2++S1
      (K2,S,MDot(msub(S,M1),tsub(S,t2), l),tsub(S,t1))
    case EModify(e1,l,e2) =>
      val (K1,S1,M1,τ1) = wk(K,T,e1)      
      val (K2,S2,M2,τ2) = wk(K1,subT(S1,T),e2)
      val τ1_ = tsub(S2,τ1)
      val t1 = fresht()
      val t2 = fresh()
      val (K3,S3) = u(K2++Map(t1->U,t2->krecord(List(l->t1))),List((t1,τ2),(t2,τ1_)))
      val S32 = S3++S2
      val S321 = S32++S1
      val t2_ = tsub(S3,t2)
      (K3,S321,MModify(msub(S32,M1),t2_,l,msub(S3,M2)),t2_)
    case ECase(E0,les) =>
      val (K0,S0,M0,τ0) = wk(K,T,E0)
      val t0 = fresh()
      foldr([Li=Ei,(Ki1,Ti1,LMs1,Lts1,K1,Tts1,S1),
        (Ki,Ti,[Li=Mi|LMs1],[Li:ti|Lts1],[ti:u|K1],[(τi,ti)|Tts1],S)]>>(
        wk(Ki1,Ti1,Ei,(Ki,Si,Mi,τi)), subT(Si,Ti1,Ti),
        union(Si,S1,S),fresh(ti)
      ),les,(K0,subT(S0,T),[],[],Kn,[],[]),(Kn,_,LMs,Lts,Kn_,Tts,S)),
      maplist({t0,S}/[(τi,ti),(τi_,(t0->ti))]>>tsub(S,τi,τi_),Tts,Tts_),
      tsub(S,τ0,τ0_), union([(τ0_,{Lts})],Tts_,Tts2),
      u(Kn_,Tts2, (Kn1,Sn1)),union(Sn1,S,S_),
      tsub(Sn1,t0,t0_),msub(S_,M0,M0_),
      maplist({S}/[Li=Mi,Li=Mi_]>>msub(S,Mi,Mi_),LMs,LMs_)
      (Kn1,S_, MCase(M0_,LMs_),t0_)
    */
    case EVariant(l,e1) =>
      val (k1,s1,m1,τ1) = wk(K,T,e1)
      val t = fresh()
      (k1+(t->kvariant(List(l->τ1))),s1,MVariant(l,m1,tx(t)),tx(t))
    /*
    case ELet(x,e1,e2) =>
      val (K1,S1,m1,τ1) = wk(K,T,e1)
      val T1 = subT(S1,T)
      val (K1_,σ1) = cls(K1,T1,τ1)
      val (K2,S2,M2,τ2) = wk(K1_,T1+(x->σ1),e2)
      val σ1_ = tsub(S2,σ1)
      (K2,S2++S1,MLet(x,σ1_,MPoly(msub(S2,m1),σ1_),M2),τ2)
    */
  }
}
