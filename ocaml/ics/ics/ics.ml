(* implementation calculs system *)
open Tmss
open Utils

type c =
  | CTrue
  | CFalse
  | CInt of int
  | Cx of x
  | CAbs of (x * c)
  | CApp of (c * c)
  | CLet of (x * c * c)
  | CRecord of c list
  | CDot of (c * c)
  | CModify of (c * c * c)
  | CVariant of (c * c)
  | CSwitch of (c * c list)

let rec show = function
  | CTrue             -> "true"
  | CFalse            -> "false"
  | CInt i            -> string_of_int i
  | Cx x              -> x
  | CAbs(x, c)        -> Printf.sprintf "λ%s.%s" x (show c)
  | CApp(c, c2)       -> Printf.sprintf "(%s %s)" (show c) (show c2)
  | CRecord(cs)       -> Printf.sprintf "{%s}" (show_cs cs)
  | CDot(c, l)        -> Printf.sprintf "%s#%s" (show c) (show l)
  | CModify(c, l, c2) -> Printf.sprintf "modify(%s,%s,%s)" (show c) (show l) (show c2)
  | CVariant(l, c)    -> Printf.sprintf "<%s=%s>" (show l) (show c)
  | CSwitch(c, cs)    -> Printf.sprintf "switch %s of %s" (show c) (show_cs cs)
  | CLet(x, c, c2)    -> Printf.sprintf "let %s = %s in %s" x (show c) (show c2)
and show_cs cs =
  String.concat "," (List.map show cs)

(* ------------------------------
 * compiler
 * ------------------------------ *)

let rec kinding(eK, q):k = match q with
  | q when List.mem_assoc q eK -> List.assoc q eK
  | TRecord(f) -> KRecord(f)
  | TVariant(f) -> KVariant(f)
  | _ -> U

let rec idxSet(t, k) = match k with
  | U -> []
  | KRecord(f) ->  f|>List.map(fun(l,_)->(l,t))
  | KVariant(f) -> f|>List.map(fun(l,_)->(l,t))

(*
let rec idxSet1(q:q):Set[(x,q)] = q match {
  case ∀(x,k,t) => idxSet(tx(x),k) ++ idxSet(t)
  case _ => Set()
}
*)
let rec idxSetK(eK) =
  List.fold_left (fun is1 (t,k) ->
    List.union_assoc is1 (idxSet(t,k))
  ) [] eK
let rec sortf(f) = f |> List.sort(fun (l1,_) (l2,_) ->String.compare l1 l2)
let rec sortk = function
  | U -> U
  | KRecord(f) -> KRecord(sortf(f))
  | KVariant(f) -> KVariant(sortf(f))
let rec sortq = function
  | TAll(ti,k,t) -> let (l,t1) = sortq(t) in ((ti,sortk k)::l,t1)
  | t -> ([],t)

let rec addIdx = function
  | TRecord(lts) -> TRecord(lts|>List.map(fun (x,t)->(x,addIdx(t))))
  | TVariant(lts) -> TVariant(lts|>List.map(fun (x,t)->(x,addIdx(t))))
  | TAll(_,_,_) as q ->
    let (l,t) = sortq(q) in
    let t2 = List.fold_right(fun tk t -> match tk with
      | (x,U) -> t
      | (x,KRecord(f))  -> List.fold_right(fun (li,ti) t1 -> TIdx(li,Tx(x),t1)) f t
      | (x,KVariant(f)) -> List.fold_right(fun (li,ti) t1 -> TIdx(li,Tx(x),t1)) f t 
    ) l (addIdx t) in
    List.fold_right (fun (t,k) t3 -> TAll(t,k,t3)) l t2
  | t -> t


let rec getci((eL:(x * (x * q)) list), (l:x), (t:q)):c =
  try
    let idxs = idxSet(t, kinding([], t)) in
    let rec find i = function
      | [] -> failwith "error"
      | (l1,t1)::ls when l = l1 && t = t1 -> CInt i
      | _::ls -> find (i+1) ls
    in
    find 1 idxs
  with _ ->
  try
    let (x,_) = eL|> List.find (fun (x, (l1, t1)) -> l = l1 && t = t1) in
    Cx x
  with _ -> failwith ("assert find index")


let rec c((eL:(x * (x * q)) list), (eT:(x * q) list), (m:m)):c = match m with
  | Mx(x) -> Cx(x)
  | MTApp(Mx(x),ts) ->
    let rec stripq((ts:q list), (q:q)):((x * q) list * q) =
      match (ts,q) with
      | ([],q) -> ([],q)
      | (t::ts,TAll(x,_,q)) -> let (s,q_) = stripq(ts,q) in (List.union_assoc s [x,t], q_)
      | (_,_) -> failwith ("assert stripq" (* +(q,ts) *))
    in
    let rec addApp((eL:(x * (x * q)) list), (s:(x * q) list), (q:q), (c:c)):c =
      match q with
      | TIdx(l,t,t2) -> (addApp(eL,s,t2,CApp(c,getci(eL,l,tsub(s,t)))):c)
      | _ -> c
    in
    let (s,t) = stripq(ts,List.assoc x eT) in addApp(eL,s,t,Cx(x))
  | MTApp(_,_) -> assert false
  | MTrue -> CTrue
  | MFalse -> CFalse
  | MInt(i) -> CInt(i)
  | MAbs(x,t,m) -> CAbs(x,c(eL,List.union_assoc eT [x,t],m))
  | MApp(m1,m2) -> CApp(c(eL,eT,m1),c(eL,eT,m2))
  | MRecord(f) -> CRecord(f|>List.map(fun (_,m) -> c(eL,eT,m)))
  | MDot(m1,t,l) -> CDot(c(eL,eT,m1),getci(eL,l,t))
  | MModify(m1,t,l,m2) -> let c1 = c(eL,eT,m1) in CModify(c1,getci(eL,l,t),c(eL,eT,m2))
  | MVariant(l,m,t) -> CVariant(getci(eL,l,t),c(eL,eT,m))
  | MCase(m,f) -> CSwitch(c(eL,eT,m),f|>List.map(fun (li,mi)->c(eL,eT,mi)))
  | MPoly(m1,t) ->
    let rec getL((eL:(x * (x * q)) list), (q:q)):((x * (x * q)) list * x list) = match q with
      | TIdx(l,ti,t) -> let x = fresh() in let (eL_,is) = getL(eL,t) in ((x,(l,ti))::eL_,x::is)
      | _ -> (eL,[])
    in
    let (_,idxs) = sortq(addIdx(t)) in
    let (eL_,is) = getL(eL,idxs) in
    List.fold_right(fun x c ->CAbs(x,c)) is (c(eL_,eT,m1))
  | MLet(x,q,m1,m2) -> CLet(x,c(eL,eT,m1),c(eL,List.union_assoc eT [x,addIdx(q)],m2))

let rec lk(eK:(q * k) list):(x * (x * q)) list =
  idxSetK(eK)|> List.map (fun (l,t)->(fresh(),(l,t)))
let show_lk lk =
  "{" ^ String.concat "," (List.map (fun (x,(t,q))-> Printf.sprintf "idx(%s,%s,%s)" x t (show_q q)) lk) ^ "}"

(* ------------------------------
 * evaluator
 * ------------------------------ *)
let rec v = function
  | CInt(_) -> true
  | CTrue -> true
  | CFalse -> true
  | CAbs(x,_) -> true
  | CRecord(cs) -> not (cs|>List.exists(fun c -> not (v c)))
  | CVariant(l,c) -> v(c)
  | _ -> false

let rec csub(s, c) = match c with
  | Cx(x) when List.mem_assoc x s -> csub(s,List.assoc x s)
  | CAbs(x,c) -> CAbs(x,csub(List.del_assoc x s,c))
  | CApp(c1,c2) -> CApp(csub(s,c1),csub(s,c2))
  | CRecord(cs) -> CRecord(cs|>List.map(fun c->csub(s,c)))
  | CDot(c,l) -> CDot(csub(s,c),csub(s,l))
  | CModify(c1,l,c2) -> CModify(csub(s,c1),csub(s,l),csub(s,c2))
  | CVariant(l,c) -> CVariant(l,csub(s,c))
  | CSwitch(c,cs) -> CSwitch(csub(s,c),cs|>List.map(fun c->csub(s,c)))
  | CLet(x,c1,c2) -> CLet(x,csub(s,c1),csub(List.del_assoc x s,c2))
  | _ -> c

let rec eval1(c:c):c = match c with
  | CApp(c1,c2) when not (v c1) -> CApp(eval1(c1),c2)
  | CApp(v1,c2) when not (v c2) -> CApp(v1,eval1(c2))
  | CLet(x,c1,c2) when not (v c1) -> CLet(x,eval1(c1),c2)
  | CRecord(cs) ->
    let rec find(hs, ls):c = match ls with
      | [] -> failwith ("error")
      | c::ls when not (v c) -> CRecord(List.rev hs @ eval1(c)::ls)
      | c::ls -> find(c::hs,ls)
    in
    find([],cs)
  | CDot(c,l) when not (v c) -> CDot(eval1(c),l)
  | CModify(c1,l,c2) when not (v c1) -> CModify(eval1(c1),l,c2)
  | CModify(v1,l,c2) when not (v c2) -> CModify(v1,l,eval1(c2))
  | CVariant(l,c) when not (v c) -> CVariant(l,eval1(c))
  | CSwitch(c,cs) when not (v c) -> CSwitch(eval1(c),cs)

  | CApp(CAbs(x,c),v1) -> csub([x,v1],c)
  | CDot(CRecord(vs),CInt(i)) -> List.nth vs (i-1)
  | CModify(CRecord(vs),CInt(i),v) ->
    let rec find(hs, l, ls):c = match ls with
      | [] -> failwith ("error")
      | c::ls when l==i -> CRecord(List.rev hs @ v::ls)
      | c::ls -> find(c::hs,l+1,ls)
    in
    find([],1,vs)
  | CSwitch(CVariant(CInt(li),v),ls) -> CApp(List.nth ls (li-1),v)
  | CLet(x,v,c) -> csub([x,v],c)
  | c -> failwith ("error")

let rec eval(c:c):c = try eval(eval1(c)) with _ -> c
