(* typed ML Style System *)
open Utils

type l = string
type x = string
type i = int
type k =
  | U
  | KRecord of (l * q) list
  | KVariant of (l * q) list
and q =
  | TBool
  | TInt
  | Tx of x
  | TArr of (q * q)
  | TRecord of (l * q) list
  | TVariant of (l * q) list
  | TAll of (x * k * q)
  | TIdx of (x * q * q)

type m =
  | Mx of x
  | MTApp of (m * q list)
  | MTrue
  | MFalse
  | MInt of i
  | MAbs of (x * q * m)
  | MApp of (m * m)
  | MRecord of (l * m) list
  | MDot of (m * q * l)
  | MModify of (m * q * l * m)
  | MVariant of (l * m * q)
  | MCase of (m * (l * m) list)
  | MPoly of (m * q)
  | MLet of (x * q * m * m)

(* Substitutions *)
let rec ksub (s,k) = match k with
  | U -> U
  | KRecord(f) -> KRecord(f |> List.map(fun (l,t)->(l,tsub(s,t))))
  | KVariant(f) -> KVariant(f |> List.map(fun (l,t)->(l,tsub(s,t))))
and tsub(s, q):q = match q with
  | Tx(x) when List.mem_assoc x s -> tsub(s,List.assoc x s)
  | TArr(q1,q2) -> TArr(tsub(s,q1),tsub(s,q2))
  | TRecord(f) -> TRecord(f|>List.map(fun (l,t)->(l,tsub(s,t))))
  | TVariant(f) -> TVariant(f|>List.map(fun (l,t)->(l,tsub(s,t))))
  | TAll(x,k,q) -> TAll(x,ksub(List.del_assoc x s,k),tsub(List.del_assoc x s,q))
  | _ -> q

let rec msub(s,m) = match m with
  | Mx(x) when List.mem_assoc x s -> msub(s,List.assoc x s)
  | MTApp(m,qs) -> MTApp(msub(s,m),qs)
  | MAbs(x,q,m) -> MAbs(x,q,msub(List.del_assoc x s,m))
  | MApp(m1,m2) -> MApp(msub(s,m1),msub(s,m2))
  | MRecord(f) -> MRecord(f|>List.map(fun (l,m)->(l,msub(s,m))))
  | MDot(m,q,l) -> MDot(msub(s,m),q,l)
  | MModify(m1,q,l,m2) -> MModify(msub(s,m1),q,l,msub(s,m2))
  | MVariant(l,m,q) -> MVariant(l,msub(s,m),q)
  | MCase(m,f) -> MCase(msub(s,m),f|>List.map(fun (l,m)->(l,msub(s,m))))
  | MPoly(m,q) -> MPoly(msub(s,m),q)
  | MLet(x,q,m1,m2) -> MLet(x,q,msub(List.del_assoc x s,m1),msub(List.del_assoc x s,m2))
  | _ -> m

let rec mtsub(s, m):m = match m with
  | MTApp(m,qs) -> MTApp(mtsub(s,m),qs|>List.map(fun q -> tsub(s,q)))
  | MAbs(x,q,m) -> MAbs(x,tsub(s,q),mtsub(s,m))
  | MApp(m1,m2) -> MApp(mtsub(s,m1),mtsub(s,m2))
  | MRecord(lMs) -> MRecord(lMs|>List.map(fun (l,m)->(l,mtsub(s,m))))
  | MDot(m,q,l) -> MDot(mtsub(s,m),tsub(s,q),l)
  | MModify(m1,q,l,m2) -> MModify(mtsub(s,m1),tsub(s,q),l,mtsub(s,m2))
  | MVariant(l,m,q) -> MVariant(l,mtsub(s,m),tsub(s,q))
  | MCase(m,lMs) -> MCase(mtsub(s,m),lMs|>List.map(fun (l,m)->(l,mtsub(s,m))))
  | MPoly(m,q) -> MPoly(mtsub(s,m),q)
  | MLet(x,q,m1,m2) -> MLet(x,tsub(s,q),mtsub(s,m1),mtsub(s,m2))
  | _ -> m

let subEq(s, eE) =
  eE|>List.map(fun(t1,t2)->(tsub(s,t1),tsub(s,t2)))
let subT(s, eT) =
  eT|>List.map(fun(x,t)->(x,tsub(s,t)))
let subK(s, eK) =
  eK|>List.map(fun(q,k)->(tsub(s,q),ksub(s,k)))
let ssub(s, s1) =
  let rec xtsub(s, x) =
    try match List.assoc x s with
    | Tx(x) -> xtsub(s,x) (* todo ssub の xは書き換え対象かよく考える *)
    | t -> failwith("ssub error")
    with _ -> x
  in
  s1|>List.map(fun(x,t)->(xtsub(s,x),tsub(s,t)))

(* Free Type variables *)

let rec ftv = function
  | Tx(x) -> [x]
  | TArr(q1,q2) -> List.union (ftv q1) (ftv q2)
  | TRecord(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f
  | TVariant(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f
  | TAll(t,k,q) -> List.del t (List.union (kftv k) (ftv q))
  | _ -> []
and kftv = function
  | U -> []
  | KRecord(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f 
  | KVariant(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f

let eftv(eK, q) =
  try
    let k = List.assoc q eK in
    List.union (ftv q) (kftv k)
  with _ -> ftv q

(* Type system *)
let i = ref 0
let reset() = i := 0
let resetn(ii:int) = i := ii
let fresh() =
  let ii = !i in
  i := 1;
  Printf.sprintf "x%d" ii

let fresht():q = Tx(fresh())

(* Kinded Unification *)

let sub(f1, f2) =
  let f1 = List.sort String.compare f1 in
  let f2 = List.sort String.compare f2 in
  f1 = List.inter f1 f2

let dom f = f|>List.map(fun(l,_)->l)

let add(f1, f2) =
  List.union(dom f1) (dom f2) |> List.map(fun l ->
    try let t1 = f1|>List.assoc l in
      try let t2 = f2|>List.assoc l in
        assert (t1 = t2);
        (l,t1)
      with _ -> (l,t1)
    with _ ->
    try let t2 = f2|>List.assoc l in (l,t2)
    with _ -> failwith "assert add"
  )

let rec u1 = function
  | (eE,eK,s,sK) when (Printf.printf "a:u1 "(*+(eE,eK,s,sK)*); false) -> assert false
  (* (i) type *)
  |((t1,t2)::eE,eK,s,sK) when t1=t2 -> (eE,eK,s,sK)
  (* (ii) *)
  |((Tx x as t,t2)::eE,eK,s,sK) when not (List.mem x (ftv t2)) && (try (List.assoc t eK)=U with _ -> false) ->
    (subEq([x,t2],eE),      subK([x,t2],List.del_assoc t eK),
     ssub([x,t2],s)@[x,t2], subK([x,t2],sK)@[t,U])
  |((Tx x as t,t2)::eE,eK,s,sK) when not (List.mem x (ftv t2)) && not (List.mem_assoc t eK) ->
    u1((t,t2)::eE,eK@[t,U],s,sK)
  |((TAll(t,eK,t1),t2)::eE,eK0,s,sK) -> u1((t1,t2)::eE,eK0@[Tx(t),eK],s,sK)
  (* (iii) record *)
  | (((Tx x1 as t1),(Tx x2 as t2))::eE,eK0,s,sK) when 
    (try match List.assoc t1 eK0, List.assoc t2 eK0 with
         | KRecord f1,KRecord f2 -> true | _ -> false with _ -> false)->
    let f1,f2 =
      match List.assoc t1 eK0, List.assoc t2 eK0 with
      | KRecord f1, KRecord f2 -> (f1,f2)
      | _ -> assert false
    in
    (subEq([x1,t2],eE @ ((List.inter (dom f1)(dom f2)) |>List.map(fun l->List.assoc l f1,List.assoc l f2))),
      subK([x1,t2],eK0|>List.del_assoc t1|>List.del_assoc t2)@[t2,ksub([x1,t2],KRecord(add(f1, f2)))],
      ssub([x1,t2],s)@[x1,t2],
      subK([x1,t2],sK)@[t1,KRecord(f1)])
  (* (iv) record2 *)
  |((Tx x1 as t1,(TRecord f2 as t2))::eE,eK0,s,sK) when
    (try match List.assoc t2 eK0 with
         | KRecord(f1) -> sub(dom(f1),dom(f2)) && not (List.mem x1 (ftv t2))
         | _ ->false
     with _ -> false) ->
    let f1 = match List.assoc t1 eK0 with KRecord f1 -> f1 | _ -> assert false in
    (subEq([x1,t2],eE@(dom(f1)|>List.map(fun l->(List.assoc l f1,List.assoc l f2)))),
      subK([x1,t2],eK0|>List.del_assoc t1),
      ssub([x1,t2],s)@[x1,t2],
      subK([x1,t2],sK)@[t1,KRecord f1])
  (* (v) record3 *)
  |((TRecord(f1),TRecord(f2))::eE,eK,s,sK) when dom(f1)=dom(f2) ->
    (eE@(dom(f1)|>List.map(fun l->(List.assoc l f1,List.assoc l f2))),eK,s,sK)
  (* (vi) variant *)
  |((Tx x1 as t1,(Tx x2 as t2))::eE,eK0,s,sK)
    when (try match List.assoc t1 eK0,List.assoc t2 eK0 with KVariant _, KVariant _ -> true | _ -> false with _ -> false) ->
    let f1,f2 = match List.assoc t1 eK0,List.assoc t2 eK0 with KVariant f1,KVariant f2 -> f1,f2 | _ -> assert false in
    (subEq([x1,t2],eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->List.assoc l f1,List.assoc l f2))),
      subK([x1,t2],eK0|>List.del_assoc t1|>List.del_assoc t2)@[t2,ksub([x1,t2],KVariant(add(f1,f2)))],
      ssub([x1,t2],s)@[x1,t2],
      subK([x1,t2],sK)@[t1,KVariant f1])
  (* (vii) variant2 *)
  |((Tx x1 as t1,(TVariant f2 as t2))::eE,eK0,s,sK)
    when (try match List.assoc t1 eK0 with
              | KVariant f1 -> sub(dom f1, dom f2) && not (List.mem x1 (ftv t2))
              | _ -> false with _ -> false) ->
    let f1 = match List.assoc t1 eK0 with KVariant(f1) -> f1 | _ -> assert false in
    (subEq([x1,t2],eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->(List.assoc l f1,List.assoc l f2)))),
      subK([x1,t2],eK0|>List.del_assoc t1),
      ssub([x1,t2],s)@[x1,t2],
      subK([x1,t2],sK)@[t1,KVariant f1])
  (* (viii) variant3 *)
  |((TVariant f1,TVariant f2)::eE,eK,s,sK) ->
    (eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->List.assoc l f1,List.assoc l f2)),eK,s,sK)
  (* (ix) arr *)
  |((TArr(t11,t21),TArr(t12,t22))::eE,eK,s,sK) ->
    (eE@[t11,t12;t21,t22],eK,s,sK)
  | _ -> failwith "assert"

let rec u = function
  | ([],eK,s,sK) -> (eK,s)
  | ((t1,t2)::eE,eK,s,sK) ->
    u(try u1((t1,t2)::eE,eK,s,sK) with _ -> u1((t2,t1)::eE,eK,s,sK))
let u(eK, eE) = u(eE,eK,[],[])

(* alorighm WK *)
let cls(eK, eT, t) = match t with
  | TAll(x,k,t) -> (eK,TAll(x,k,t))
  | t ->
    let ts = eftv(eK, t) |> List.delete (eftv(eK, TRecord eT)) in
    let eK1 = eK |>List.filter(function (Tx x,_)->List.mem x ts | _ ->false) in
    (eK |> List.delete_assoc (List.keys eK1),
     List.fold_right(function (Tx x,k) -> (fun t -> TAll(x,k,t)) | _ -> (fun _ -> assert false)) eK1 t )


let rec wk(eK, eT, e) = match e with
  | Mss.EInt(i) -> (eK,[],MInt(i),TInt)
  | Mss.ETrue -> (eK,[],MTrue,TBool)
  | Mss.EFalse -> (eK,[],MFalse,TBool)
  | Mss.Ex(x) ->
    let rec foldxq(q, eK, s) = match q with
      | TAll(t_,k,q) ->
        let ti = fresht() in
        let (ts,q_,eK_,s_) = foldxq(q,eK,s) in
        (ti::ts,q_,eK_@[ti,k],s_@[t_, ti])
      | q -> ([],q,eK,s)
     in
    let (ts,t,eK_,s)=foldxq(List.assoc x eT,[],[]) in
    (List.union_assoc eK (List.map(fun (ti,ki)->(ti,ksub(s,ki))) eK_),[],
      (if ts=[] then Mx x else MTApp(Mx(x),ts)),tsub(s,t))
  | Mss.EAbs(x,e1) ->
    let t = fresht() in
    let (eK1,s1,m1,t1) = wk(eK@[t,U],eT@[x,t],e1) in
    let t_ = tsub(s1,t) in
    (eK1,s1,MAbs(x,t_,m1),TArr(t_,t1))
  | Mss.EApp(e1,e2) ->
    let (eK1,s1,m1,q1) = wk(eK,eT,e1) in
    let (eK2,s2,m2,q2) = wk(eK1,subT(s1,eT),e2) in
    let t = fresht() in
    let (eK3,s3) = u(eK2,[tsub(s2,q1),TArr(q2,t)]) in
    let s32 = List.union s3 s2 in
    (eK3,List.union s32 s1,MApp(mtsub(s32,m1), mtsub(s3,m2)),tsub(s3,t))
  | Mss.ERecord(les) ->
    let (_,kn,sn,lms,lts) = List.fold_left(
      fun (eT,eK,s,lms,lqs) (l1,e1) ->
        let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
        (subT(s1,eT),eK1,List.union s1 s,(l1,m1)::lms,(l1,t1)::lqs)
      ) (eT,eK,[],[],[]) les
    in
    (kn,sn,MRecord(List.rev lms),TRecord(List.rev lts))
  | Mss.EDot(e1,l) ->
    let (eK1,s1,m1,t0) = wk(eK,eT,e1) in
    let t1 = fresht() in
    let t2 = fresht() in
    let (eK2,s2) = u(List.union_assoc eK1 [t1,U;t2,KRecord[l,t1]],[t2,t0]) in
    let s = List.union_assoc s2 s1 in
    (eK2,s,MDot(mtsub(s,m1),tsub(s,t2), l),tsub(s,t1))
  | Mss.EModify(e1,l,e2) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let (eK2,s2,m2,t2) = wk(eK1,subT(s1,eT),e2) in
    let (t1_,t3,t4) = (tsub(s2,t1), fresht(), fresht()) in
    let (eK3,s3) = u(List.union_assoc eK2 [t3,U;t4,KRecord([l,t3])],[t3,t2;t4,t1_]) in
    let s32 = List.union_assoc s3 s2 in
    let t4_ = tsub(s3,t4) in
    (eK3,List.union_assoc s32 s1,MModify(mtsub(s32,m1),t4_,l,mtsub(s3,m2)),t4_)
  | Mss.ECase(e0,les) ->
    let (eK0,s0,m0,q0) = wk(eK,eT,e0) in
    let t0 = fresht() in
    let (eKn,_,lms,lts,eKn_,tts,s) = List.fold_right(
      fun (li,ei) (eKi1,eTi1,ms1,lts1,eK1,tts1,s1) ->
        let (eKi,si,mi,qi) = wk(eKi1,eTi1,ei) in
        let ti = fresht() in
        (eKi,
         subT(List.union_assoc si s1,eTi1),
         (li,mi)::ms1,
         (li,ti)::lts1,
         List.union_assoc eK1 [ti,U],
         (qi,TArr(ti,t0))::tts1,
         List.union_assoc si s1)
    ) les (eK0,subT(s0,eT),[],[],[],[],s0)
    in
    let (eKn1,sn1) = u(List.union_assoc eKn eKn_,
      (tsub(s|>List.delete_assoc(List.keys s0),q0),TVariant(lts))::
      (tts|>List.map(fun (qi,ti) -> (tsub(s,qi),ti)))) in
    (eKn1,List.union_assoc sn1 s, MCase(mtsub(List.union_assoc sn1 s,m0),lms|>List.map(fun(li,mi)->(li,mtsub(s,mi)))),tsub(sn1,t0))
  | Mss.EVariant(l,e1) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let t = fresht() in
    (List.union_assoc eK1 [t,KVariant[l,t1]],s1,MVariant(l,m1,t),t)
  | Mss.ELet(x,e1,e2) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let eT1 = subT(s1,eT) in
    let (k1_,q1) = cls(eK1,eT1,t1) in
    let (eK2,s2,m2,t2) = wk(k1_,List.union_assoc eT1 [x,q1],e2) in
    let q1_ = tsub(s2,q1) in
    (eK2,List.union_assoc s2 s1,MLet(x,q1_,MPoly(mtsub(s2,m1),q1_),m2),t2)
