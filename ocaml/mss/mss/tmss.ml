(* typed ML Style System *)
open Utils

type l = string
type x = string
type i = int
type k =
  | U
  | KRecord of ft
  | KVariant of ft
and q =
  | TBool
  | TInt
  | Tx of x
  | TArr of (q * q)
  | TRecord of ft
  | TVariant of ft
  | TAll of (x * k * q)
  | TIdx of (x * q * q)
and ft = (l * q) list

let rec show_k : k -> string =
  function
  | U -> "U"
  | KRecord(lqs) -> Printf.sprintf "{{%s}}" (show_lqs lqs)
  | KVariant(lqs) -> Printf.sprintf "<<%s>>" (show_lqs lqs)
and show_q : q -> string =
  function
  | TBool -> "bool"
  | TInt -> "int"
  | Tx x -> x
  | TArr(q, q2) -> Printf.sprintf "(%s->%s)" (show_q q) (show_q q2)
  | TRecord lqs -> Printf.sprintf "{%s}" (show_lqs lqs)
  | TVariant lqs -> Printf.sprintf "<%s>" (show_lqs lqs)
  | TAll(x, k, q) -> Printf.sprintf "∀%s::%s.%s" x (show_k k) (show_q q)
  | TIdx(x, q, q2) -> Printf.sprintf "idx(%s,%s)=>%s" x (show_q q) (show_q q2)
and show_lqs : ft -> string =
  fun lqs ->
    String.concat "," (lqs|>List.map(fun (l,q)->l^":"^(show_q q)))

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
type f = (l * m) list

let rec show : m -> string =
  function
  | MTApp(m, qs)      -> Printf.sprintf "(%s!%s)" (show m) (show_qs qs)
  | MTrue             -> "true"
  | MFalse            -> "false"
  | MInt i            -> string_of_int i
  | Mx x              -> x
  | MAbs(x,q,m)       -> Printf.sprintf "λ%s:%s.%s" x (show_q q) (show m)
  | MApp(m, m2)       -> Printf.sprintf "(%s %s)" (show m) (show m2)
  | MRecord(lms)      -> Printf.sprintf "{%s}" (show_lms lms)
  | MDot(m,q,l)       -> Printf.sprintf "(%s:%s#%s)" (show m) (show_q q) l
  | MModify(m,q,l,m2) -> Printf.sprintf "modify(%s:%s,%s,%s)" (show m) (show_q q) l (show m2)
  | MVariant(l, m, q) -> Printf.sprintf "(<%s=%s>:%s)" l (show m) (show_q q)
  | MCase(m, lms)     -> Printf.sprintf "case %s of <%s>" (show m) (show_lms lms)
  | MPoly(m, q)       -> Printf.sprintf "Poly(%s:%s)" (show m) (show_q q)
  | MLet(x, q, m, m2) -> Printf.sprintf "let %s:%s = %s in %s" x (show_q q) (show m) (show m2)
and show_lms : f -> string =
  fun lms ->
    String.concat "," (List.map(fun(l,m)->l^"="^show m) lms)
and show_qs : q list -> string =
  fun qs ->
    String.concat "!" (List.map show_q qs)

(* Substitutions *)
module Q = MMake(struct
  type t = q
  let compare q1 q2 = match q1,q2 with
    | Tx(x1),Tx(x2) -> String.compare x1 x2
    | _ -> assert false
end)

(* type s = m M.t *)
type sq = q M.t
type eK = k Q.t
type eT = q M.t
type eE = (q * q) list

let show_eK : eK -> string =
  fun eK ->
    "{" ^ String.concat "," (List.map(fun (t,k) -> show_q t ^ "::" ^ show_k k) (eK|>Q.bindings)) ^ "}"

let rec ksub : (sq * k) -> k =
  fun (s,k) -> match k with
  | U -> U
  | KRecord(f) -> KRecord(f |> List.map(fun (l,t)->(l,tsub(s,t))))
  | KVariant(f) -> KVariant(f |> List.map(fun (l,t)->(l,tsub(s,t))))
and tsub : (sq * q) -> q =
  fun (s, q) -> match q with
  | Tx(x) when M.mem x s -> tsub(s,M.find x s)
  | TArr(q1,q2) -> TArr(tsub(s,q1),tsub(s,q2))
  | TRecord(f) -> TRecord(f|>List.map(fun (l,t)->(l,tsub(s,t))))
  | TVariant(f) -> TVariant(f|>List.map(fun (l,t)->(l,tsub(s,t))))
  | TAll(x,k,q) -> TAll(x,ksub(M.remove x s,k),tsub(M.remove x s,q))
  | _ -> q
(*
let rec msub : (s * m) -> m =
  fun (s,m) -> match m with
  | Mx(x) when M.mem x s -> msub(s,M.find x s)
  | MTApp(m,qs) -> MTApp(msub(s,m),qs)
  | MAbs(x,q,m) -> MAbs(x,q,msub(M.remove x s,m))
  | MApp(m1,m2) -> MApp(msub(s,m1),msub(s,m2))
  | MRecord(f) -> MRecord(f|>List.map(fun (l,m)->(l,msub(s,m))))
  | MDot(m,q,l) -> MDot(msub(s,m),q,l)
  | MModify(m1,q,l,m2) -> MModify(msub(s,m1),q,l,msub(s,m2))
  | MVariant(l,m,q) -> MVariant(l,msub(s,m),q)
  | MCase(m,f) -> MCase(msub(s,m),f|>List.map(fun (l,m)->(l,msub(s,m))))
  | MPoly(m,q) -> MPoly(msub(s,m),q)
  | MLet(x,q,m1,m2) -> MLet(x,q,msub(M.remove x s,m1),msub(M.remove x s,m2))
  | _ -> m
*)
let rec mtsub : (sq * m) -> m =
  fun (s, m) -> match m with
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
let subEq : (sq * eE) -> eE = fun (s, eE) -> eE|>List.map(fun(t1,t2)->(tsub(s,t1),tsub(s,t2)))
let subT : (sq * eT) -> eT = fun (s, eT) -> eT|>M.map(fun t-> tsub(s,t))
let subK : (sq * eK) -> eK = fun (s, eK) -> eK|>Q.bindings|>List.map(fun(q,k)->(tsub(s,q),ksub(s,k)))|>Q.of_list
let ssub : (sq * sq) -> sq = fun (s, s1) ->
  let rec xtsub : (sq * x) -> x = fun (s, x) ->
    try match M.find x s with
    | Tx(x) -> xtsub(s,x) (* todo ssub の xは書き換え対象かよく考える *)
    | t -> failwith("ssub error")
    with _ -> x
  in
  s1|>M.bindings|>List.map(fun (x, t)->(xtsub(s,x),tsub(s,t)))|>M.of_list

(* Free Type variables *)
type ftv = x list
let rec ftv : q -> ftv =
  function
  | Tx(x) -> [x]
  | TArr(q1,q2) -> List.union (ftv q1) (ftv q2)
  | TRecord(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f
  | TVariant(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f
  | TAll(t,k,q) -> List.del t (List.union (kftv k) (ftv q))
  | _ -> []
and kftv : k -> ftv =
  function
  | U -> []
  | KRecord(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f 
  | KVariant(f) -> List.fold_left (fun tv (_,m) -> List.union tv (ftv m)) [] f

let eftv : (eK * q) -> ftv =
  fun (eK, q) ->
  try
    let k = Q.find q eK in
    List.union (ftv q) (kftv k)
  with _ -> ftv q

(* Type system *)
let i : int ref = ref 0
let reset : unit -> unit = fun () -> i := 0
let resetn : int -> unit = fun ii -> i := ii
let fresh : unit -> x = fun () ->
  let ii = !i in
  i := !i + 1;
  Printf.sprintf "x%d" ii

let fresht : unit -> q = fun () -> Tx(fresh())

(* Kinded Unification *)
type dom = x list
let sub : (dom * dom) -> bool =
  fun (dom1, dom2) ->
  let dom1 = List.sort String.compare dom1 in
  let dom2 = List.sort String.compare dom2 in
  dom1 = List.inter dom1 dom2

let dom : ft -> dom =
  fun ft -> ft|>List.map(fun(l,_)->l)

let add : (ft * ft) -> ft =
  fun (f1, f2) ->
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

let rec u1 : (eE * eK * sq * eK) -> (eE * eK * sq * eK) =
  function
  (* | (eE,eK,s,sK) when (Printf.printf "a:u1 (eE,%s,s,sK)\n" (show_eK eK); false) -> assert false *)
  (* (i) type *)
  | ((t1,t2)::eE,eK,s,sK) when t1=t2 -> (eE,eK,s,sK)
  (* (ii) *)
  | ((Tx x as t,t2)::eE,eK,s,sK) when not (List.mem x (ftv t2)) && (try (Q.find t eK)=U with _ -> false) ->
    (subEq(M.singleton x t2,eE),            subK(M.singleton x t2,Q.remove t eK),
     ssub(M.singleton  x t2,s)|>M.add x t2, subK(M.singleton x t2,sK)|>Q.add t U)
  | ((Tx x as t,t2)::eE,eK,s,sK) when not (List.mem x (ftv t2)) && not (Q.mem t eK) ->
    u1((t,t2)::eE,eK|>Q.add t U,s,sK)
  | ((TAll(t,eK,t1),t2)::eE,eK0,s,sK) -> u1((t1,t2)::eE,eK0|>Q.add (Tx t) eK,s,sK)
  (* (iii) record *)
  | (((Tx x1 as t1),(Tx x2 as t2))::eE,eK0,s,sK) when 
    (try match Q.find t1 eK0, Q.find t2 eK0 with
         | KRecord f1,KRecord f2 -> true | _ -> false with _ -> false)->
    let f1,f2 =
      match Q.find t1 eK0, Q.find t2 eK0 with
      | KRecord f1, KRecord f2 -> (f1,f2)
      | _ -> assert false
    in
    (subEq(M.singleton x1 t2,eE @ ((List.inter (dom f1)(dom f2)) |>List.map(fun l->List.assoc l f1,List.assoc l f2))),
      subK(M.singleton x1 t2,eK0|>Q.remove t1|>Q.remove t2)|>Q.add t2 (ksub(M.singleton x1 t2,KRecord(add(f1, f2)))),
      ssub(M.singleton x1 t2,s)|>M.add x1 t2,
      subK(M.singleton x1 t2,sK)|>Q.add  t1 (KRecord f1))
  (* (iv) record2 *)
  | ((Tx x1 as t1,(TRecord f2 as t2))::eE,eK0,s,sK) when
    (try match Q.find t1 eK0 with
         | KRecord(f1) -> sub(dom(f1),dom(f2)) && not (List.mem x1 (ftv t2))
         | _ -> false
     with _ -> false) ->
    let f1 = match Q.find t1 eK0 with KRecord f1 -> f1 | _ -> assert false in
    (subEq(M.singleton x1 t2,eE@(dom(f1)|>List.map(fun l->(List.assoc l f1,List.assoc l f2)))),
      subK(M.singleton x1 t2,eK0|>Q.remove t1),
      ssub(M.singleton x1 t2,s)|>M.add x1 t2,
      subK(M.singleton x1 t2,sK)|>Q.add t1 (KRecord f1))
  (* (v) record3 *)
  | ((TRecord(f1),TRecord(f2))::eE,eK,s,sK) when dom(f1)=dom(f2) ->
    (eE@(dom(f1)|>List.map(fun l->(List.assoc l f1,List.assoc l f2))),eK,s,sK)
  (* (vi) variant *)
  | ((Tx x1 as t1,(Tx x2 as t2))::eE,eK0,s,sK)
    when (try match Q.find t1 eK0,Q.find t2 eK0 with KVariant _, KVariant _ -> true | _ -> false with _ -> false) ->
    let f1,f2 = match Q.find t1 eK0,Q.find t2 eK0 with KVariant f1,KVariant f2 -> f1,f2 | _ -> assert false in
    (subEq(M.singleton x1 t2,eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->List.assoc l f1,List.assoc l f2))),
      subK(M.singleton x1 t2,eK0|>Q.remove t1|>Q.remove t2)|>Q.add t2 (ksub(M.singleton x1 t2,KVariant(add(f1,f2)))),
      ssub(M.singleton x1 t2,s)|>M.add x1 t2,
      subK(M.singleton x1 t2,sK)|>Q.add  t1 (KVariant f1))
  (* (vii) variant2 *)
  | ((Tx x1 as t1,(TVariant f2 as t2))::eE,eK0,s,sK)
    when (try match Q.find t1 eK0 with
              | KVariant f1 -> sub(dom f1, dom f2) && not (List.mem x1 (ftv t2))
              | _ -> false with _ -> false) ->
    let f1 = match Q.find t1 eK0 with KVariant(f1) -> f1 | _ -> assert false in
    (subEq(M.singleton x1 t2,eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->(List.assoc l f1,List.assoc l f2)))),
      subK(M.singleton x1 t2,eK0|>Q.remove t1),
      ssub(M.singleton x1 t2,s)|>M.add x1 t2,
      subK(M.singleton x1 t2,sK)|>Q.add t1 (KVariant f1))
  (* (viii) variant3 *)
  | ((TVariant f1,TVariant f2)::eE,eK,s,sK) ->
    (eE@((List.inter (dom f1) (dom f2))|>List.map(fun l->List.assoc l f1,List.assoc l f2)),eK,s,sK)
  (* (ix) arr *)
  | ((TArr(t11,t21),TArr(t12,t22))::eE,eK,s,sK) ->
    (eE@[t11,t12;t21,t22],eK,s,sK)
  | ((t1,t2)::_,_,_,_) -> failwith (Printf.sprintf "assert (%s,%s)" (show_q t1) (show_q t2))

let rec u : (eE * eK * sq * eK) -> (eK * sq) =
  function
  | ([],eK,s,sK) -> (eK,s)
  | ((t1,t2)::eE,eK,s,sK) ->
    u(try u1((t1,t2)::eE,eK,s,sK) with _ -> u1((t2,t1)::eE,eK,s,sK))
let u : (eK * eE) -> (eK * sq) =
  fun (eK, eE) ->
  u(eE,eK,M.empty,Q.empty)

(* alorighm WK *)
let cls : (eK * eT * q) -> (eK * q) =
  fun (eK, eT, t) -> match t with
  | TAll(x,k,t) -> (eK,TAll(x,k,t))
  | t ->
    let ts = eftv(eK, t) |> List.delete (eftv(eK, TRecord(eT|>M.bindings))) in
    let eK1 = eK |> Q.filter (function (Tx x) -> fun _ -> List.mem x ts | _ -> fun _ ->false) in
    (Q.diff eK eK1,
     Q.fold(function (Tx x) -> (fun k t -> TAll(x,k,t)) | _ -> (fun _ _ -> assert false)) eK1 t )

let rec wk : (eK * eT * Mss.e) -> (eK * eT * m * q) =
  fun (eK, eT, e) -> match e with
  | Mss.EInt(i) -> (eK,M.empty,MInt(i),TInt)
  | Mss.ETrue -> (eK,M.empty,MTrue,TBool)
  | Mss.EFalse -> (eK,M.empty,MFalse,TBool)
  | Mss.Ex(x) ->
    let rec foldxq(q, eK, s) = match q with
      | TAll(t_,k,q) ->
        let ti = fresht() in
        let (ts,q_,eK_,s_) = foldxq(q,eK,s) in
        (ti::ts,q_,eK_|>Q.add ti k,s_|>M.add t_ ti)
      | q -> ([],q,eK,s)
     in
    let (ts,t,eK_,s)=foldxq(M.find x eT,Q.empty,M.empty) in
    (Q.union eK (Q.map(fun ki->ksub(s,ki)) eK_),M.empty,
      (if ts=[] then Mx x else MTApp(Mx(x),ts)),tsub(s,t))
  | Mss.EAbs(x,e1) ->
    let t = fresht() in
    let (eK1,s1,m1,t1) = wk(eK|>Q.add t U,eT|>M.add x t,e1) in
    let t_ = tsub(s1,t) in
    (eK1,s1,MAbs(x,t_,m1),TArr(t_,t1))
  | Mss.EApp(e1,e2) ->
    let (eK1,s1,m1,q1) = wk(eK,eT,e1) in
    let (eK2,s2,m2,q2) = wk(eK1,subT(s1,eT),e2) in
    let t = fresht() in
    let (eK3,s3) = u(eK2,[tsub(s2,q1),TArr(q2,t)]) in
    let s32 = M.union s3 s2 in
    (eK3,M.union s32 s1,MApp(mtsub(s32,m1), mtsub(s3,m2)),tsub(s3,t))
  | Mss.ERecord(les) ->
    let (_,kn,sn,lms,lts) = List.fold_left(
      fun (eT,eK,s,lms,lqs) (l1,e1) ->
        let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
        (subT(s1,eT),eK1,M.union s1 s,(l1,m1)::lms,(l1,t1)::lqs)
      ) (eT,eK,M.empty,[],[]) les
    in
    (kn,sn,MRecord(List.rev lms),TRecord(List.rev lts))
  | Mss.EDot(e1,l) ->
    let (eK1,s1,m1,t0) = wk(eK,eT,e1) in
    let t1 = fresht() in
    let t2 = fresht() in
    let (eK2,s2) = u(eK1|>Q.add_list[t1,U;t2,KRecord[l,t1]],[t2,t0]) in
    let s = M.union s2 s1 in
    (eK2,s,MDot(mtsub(s,m1),tsub(s,t2), l),tsub(s,t1))
  | Mss.EModify(e1,l,e2) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let (eK2,s2,m2,t2) = wk(eK1,subT(s1,eT),e2) in
    let (t1_,t3,t4) = (tsub(s2,t1), fresht(), fresht()) in
    let (eK3,s3) = u(eK2|>Q.add_list [t3,U;t4,KRecord([l,t3])],[t3,t2;t4,t1_]) in
    let s32 = M.union s3 s2 in
    let t4_ = tsub(s3,t4) in
    (eK3,M.union s32 s1,MModify(mtsub(s32,m1),t4_,l,mtsub(s3,m2)),t4_)
  | Mss.ECase(e0,les) ->
    let (eK0,s0,m0,q0) = wk(eK,eT,e0) in
    let t0 = fresht() in
    let (eKn,_,lms,lts,eKn_,tts,s) = List.fold_right(
      fun (li,ei) (eKi1,eTi1,ms1,lts1,eK1,tts1,s1) ->
        let (eKi,si,mi,qi) = wk(eKi1,eTi1,ei) in
        let ti = fresht() in
        (eKi,
         subT(M.union si s1,eTi1),
         (li,mi)::ms1,
         (li,ti)::lts1,
         eK1 |>Q.add ti U,
         (qi,TArr(ti,t0))::tts1,
         M.union si s1)
    ) les (eK0,subT(s0,eT),[],[],Q.empty,[],s0)
    in
    let (eKn1,sn1) = u(Q.union eKn eKn_,
      (tsub(M.diff s s0,q0),TVariant(lts))::
      (tts|>List.map(fun (qi,ti) -> (tsub(s,qi),ti)))) in
    (eKn1,M.union sn1 s,
     MCase(mtsub(M.union sn1 s,m0),
           lms|>List.map(fun(li,mi)->(li,mtsub(s,mi)))),
     tsub(sn1,t0))
  | Mss.EVariant(l,e1) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let t = fresht() in
    (eK1|>Q.add t (KVariant[l,t1]),s1,MVariant(l,m1,t),t)
  | Mss.ELet(x,e1,e2) ->
    let (eK1,s1,m1,t1) = wk(eK,eT,e1) in
    let eT1 = subT(s1,eT) in
    let (k1_,q1) = cls(eK1,eT1,t1) in
    let (eK2,s2,m2,t2) = wk(k1_,M.add x q1 eT1,e2) in
    let q1_ = tsub(s2,q1) in
    (eK2,M.union s2 s1,MLet(x,q1_,MPoly(mtsub(s2,m1),q1_),m2),t2)
