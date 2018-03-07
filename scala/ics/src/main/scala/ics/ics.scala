package ics

// 4. COMPILATION
object ics {
  // implementation calculs system
  import mss2._

  // 4.1 Implementation Calculus : λlet,[]
  /*
  trait Ï
  case class ÏI(x:x) extends Ï
  case class Ïi(i:Int) extends Ï
  */
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
  //case class CIAbs(l:C,c:C) extends C
  //case class CIApp(c:C,l:C) extends C

  //v ::= cb | λ(x,'C') | record(v) | {['Ï'=v]} | λI('I','C'). // (for some C' such that C'↓C').//todo

  def v(c:C):Boolean = c match {
    case c if cb(c) => true
    case CAbs(x,_) => true
    case CRecord(cs) => !cs.exists{case(c)=> !v(c)}
    case CVariant(l,c) => v(c)
    //case CIAbs(x,_) => true
    case _ => false
  }
  def i(c:C)   = c match {case CInt(_) => true case _ => false}
  def cb(c:C)  = c match {case CTrue => true case CFalse => true case _ => i(c)}
  def x(c:C)   = c match {case Cx(_)=>true case _=>false}
  def c(c:Any) = c match {case _:C=>true case _=>false}

  /*
  C ::= x | cb |λ(x,'C') | ('C' $ 'C') | (let(x='C'); 'C') | record('C') | 'C'#['Ï']
      | modify('C','Ï','C') | {['Ï'='C']} | switch('C', record('C')) | λI('I','C') | ('C' $ 'Ï').
  */
  // Fig. 12. Call-by-value evaluation operational semantics of λlet,[].

  /*EV[] ::= [·] | EV[] C | V EV[] | let x=EV[] in C | {V,···,V,EV[],···} | EV[][Ï]
          | modify(EV[],I,C) | modify(V,Ï,EV[]) | <Ï=EV[]> | switch EV[] of C,···,C
          | EV[] Ï | λI.EV[]*/

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
        case c::ls if !v(c) => (c,{c=>CRecord(hs.reverse:::c::ls)})
        case c::ls => find(c::hs,ls)
      }
      find(List(),cs)
    case CDot(c,l) =>
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
  /*
  EV[(λx.C) V]                                 ⟶ EV[[V/x]C]
  EV[{V1,···,Vn}[i]]                           ⟶ EV[Vi]
  EV[modify({V1,···,Vi−1,Vi,Vi+1,···,Vn},i,V)] ⟶ EV[{V1,···,Vi−1,V,Vi+1,···,Vn}]
  EV[switch <i=V> of C1,···,Cn]                ⟶ EV[Ci V]
  //EV[(λI.C) Ï]                                ⟶ EV[[Ï/I]C] if C↓C
  EV[let x=V in C]                             ⟶ EV[[V/x]C]
  */
  /*
  ev(λ(X,C)$V)                ⟶ ev(C_)          :- v(V),csub([V/X],C,C_).
  ev(Vs#[I])                  ⟶ ev(Vi)          :- nth1(I,Vs,Vi).
  ev(modify([_ |LS],1,N))     ⟶ ev([N|LS]).
  ev(modify([Mi|LS],I,N))     ⟶ ev([Mi|LS_])    :- I > 1, I_ is I - 1, ev(modify(LS,I_,N)) ⟶ ev(LS_).
  ev(switch({[I=V]},Cs))      ⟶ ev(Ci $ V)      :- nth1(I,Cs,Ci).
  ev(λ(I,C)$Ï)                ⟶ ev(C_)          :- 'Ï'(Ï),csub([Ï/I],C,C_).
  ev(let(X = V); C)           ⟶ ev(C_)          :- csub([V/X],C,C_).
  */
  def ev1(c:C):C = {
    c match {
    case CApp(CAbs(x,c),v1) if v(v1) => csub(Map(x->v1),c)
    case CDot(CRecord(vs),CInt(i)) => vs(i-1)
    case CModify(CRecord(vs),CInt(i),v) =>
      def find(hs:List[C],l:Int,ls:List[C]):C = ls match {
        case List() => CRecord(hs.reverse)
        case c::ls if l==i => println(CRecord(hs.reverse:::v::ls)); CRecord(hs.reverse:::v::ls)
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
    f(ev1(c1))
  } catch {
    case _:Throwable => ev1(c)
  }
  def eval(c:C):C = try {
    eval(eval1(c))
  } catch {
    case _:Throwable => c
  }
  /*
  csub(S,λI(X,C),λI(X,C_)) :- !,subtract(S,[_/X],S_),csub(S_,C,C_).
  */
  def csub(S:Map[x,C],c:C):C = c match {
    case Cx(x) if S.contains(x) => csub(S,S(x))
    case Cx(x) => Cx(x)
    case c if cb(c) => c
    case CAbs(x,c) => CAbs(x,csub(S - x,c))
    case CApp(c1,c2) => CApp(csub(S,c1),csub(S,c2))
    case CRecord(cs) => CRecord(cs.map{(c)=>csub(S,c)})
    case CDot(c,l) => CDot(csub(S,c),l)
    case CModify(c1,l,c2) => CModify(csub(S,c1),l,csub(S,c2))
    case CVariant(l,c) => CVariant(l,csub(S,c))
    case CSwitch(c,cs) => CSwitch(csub(S,c),cs.map{(c)=>csub(S,c)})
    case CLet(x,c1,c2) => CLet(x,csub(S,c1),csub(S,c2))
  }

  /*
  % Fig. 6. Kinding rules for the ML-style type inference system λlet,#.
  K ⊢ t:ks :- t(t),member(t:ks1,K),append(ks,_,ks1), ks \= [].
  _ ⊢ ts:ks :- maplist([l:t,l:t]>>!,ts,ks).
  %_ ⊢ ts:[li:ti] :- member(li:ti,ts).
  K ⊢ t:{ks} :- t(t),member(t:{ks1},K),append(ks,_,ks1), ks \= [].
  _ ⊢ {ts}:{ks} :-  maplist([l:t,k:t]>>!,ts,ks).
  %_ ⊢ {ts}:{[li:ti]} :- member(li:ti,ts).
  _ ⊢ τ:u :- τ(τ).
  */
  def kinding(K:Map[σ,k],σ:σ):k = σ match {
    case t if K.contains(t) => K(σ)
    case trecord(f) => krecord(f)
    case tvariant(f) => kvariant(f)
    case _ => U
  }
  /*
  // Fig. 13. Typing rules for the implementation calculus λlet,[].

  // L ⊢ Ï : idx(l,τ)   index judgment

  L ⊢ I : idx(l,τ) :- 'I'(I), member(I:idx(l,τ),L),l(l),τ(τ). // IVAR
  _ ⊢ i : idx(li,Record) :- i(i),nth1(i,Record,li:_). // ICONST1
  _ ⊢ i : idx(li,{Variant}) :- i(i),nth1(i,Variant,li:_). // ICONST2
  */


  // ------------------------------
  // compiler
  // ------------------------------

  // 4.3 Compilation Algorithm

  /*
  idxSet(t:u,[]).
  idxSet(t:F,Is) :- maplist([L:_,idx(L,t)]>>!,F,Is).
  idxSet(t:{F},Is) :- maplist([L:_,idx(L,t)]>>!,F,Is).
  idxSet(∀(t,k,τ),Is) :- idSet(t:k,Is1),idxSet(τ,Is2),union(Is1,Is2,Is).
  idxSet(K,Is) :- foldl([t:k,Is1,Is3]>>(idxSet(t:k,Is2),union(Is1,Is2,Is3)),K,[],Is).
  */
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
  /*
  getL(L,idx(li,ti,t),[Ii:idx(li,ti)|L_],[Ii|Is]) :- fresh(Ii),getL(L,t,L_,Is). 
  getL(L,_,L,[]).
  */
  def getL(L:List[(x,(x,σ))],σ:σ):(List[(x,(x,σ))],List[x]) = σ match {
    case idx(li,ti,t) =>
      val ii = fresh()
      val (l_,is) = getL(L,t)
      ((ii->(li,ti))::l_,ii::is)
    case _ => (L,List())
  }
  /*
  // この定義は、次のように型の割り当てに拡張されます: (T)* = {x : (T(x))* |x ∈ dom(T)}
  T *= R :- maplist([x:t,x:t_]>> t *= t_,T,R).
  Q *= R :- getT(Q,L,T),L\=[],T*=T1,foldr(bbb1,L,T1,T2),foldr([t:K,T3,∀(t,K,T3)]>>!,L,T2,R).
  T *= T.
  bbb1(t:u,T,T) :- !.
  bbb1(t:K,T,R) :- foldr([li:ti,T1,idx(li,t,T1)]>>!,K,T,R).
  */

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

  /*
  addλ([],t,t).
  addλ([Ii|Is],t,λ(Ii,t_)) :- addλ(Is,t,t_).
  */
  def addλ(l:List[x],c:C):C = l match {
    case List() => c
    case ii::is => CAbs(ii,addλ(is,c))
  }
  /*
  mks(σ,[],[],σ).
  mks(∀(t,_,σ),[τ|τs],[τ/t|S],σ_) :- mks(σ,τs,S,σ_).
  */
  def mks(σ:σ,τs:List[σ]):(Map[x,σ],σ) = (σ,τs) match {
    case (σ,List()) => (Map(),σ)
    case (∀(t,_,σ),τ::τs) => val(s,σ_) =mks(σ,τs); (s+(t->τ),σ_)
    case (_,_) => throw new Exception("assert")
  }
  /*
  cdot(L,S,xi,idx(l,t,t2),xi_) :-
    tsub(S,t,Sti),
    [] ⊢ Sti:ks,!,idxSet(Sti:ks,Idxs),(nth1(Ï,Idxs,idx(l,Sti)); member(Ï:idx(l,Sti),L)),
    cdot(L,S,xi$Ï,t2,xi_).
  cdot(_,_,xi,_,xi).
  */
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
    //c(L,T,x1!τ1, x_) :- xts([],x1!τ1,x!τs),member(x: σ, T),mks(σ,τs,S,σ_), cdot(L,S,x,σ_,x_).
    case MTApp(x1,τ1) =>
      val (Mx(x),τs) = xts(M,List())
      println("xts x="+x+"! τs="+τs)
      val σ = T(x)
      println("σ="+σ)
      val (s,σ_) = mks(σ,τs)
      println("mks s="+s+", σ_="+σ_)
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
    //c(L,T,({[l=M]}:τ),{[Ï=C]}) :- c(L,T,M,C), [] ⊢ τ:ks,idxSet(τ:ks,Idxs),(nth1(Ï,Idxs,idx(l,τ));member(Ï:idx(l,τ),L)).
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
    //c(L,T,case(M,{lMs}), switch(C,Cs)) :- c(L,T,M,C), maplist({L,T}/[li=Mi,Ci]>>c(L,T,Mi,Ci), lMs,Cs).
    case MCase(m,f) =>
      val c1 = c(L,T,m)
      CSwitch(c1,f.map{case(li,mi)=>c(L,T,mi)})
    case MPoly(m1,t) => val (_,idxs) = getT(rep(t)); val (l_,is) = getL(L,idxs); addλ(is,c(l_,T,m1))
    case MLet(x,σ,m1,m2) => CLet(x,c(L,T,m1),c(L,T+(x->rep(σ)),m2))
  }

  /*
  lk(K,LK) :- idxSet(K,Is), maplist([idx(l,t),L:idx(l,t)]>>fresh(L),Is,LK).
  */
  def lk(K:Map[σ,k]):List[(x,(x,σ))] =
    idxSet(K).toList.map{case(l,t)=>(fresh(),(l,t))}

}
