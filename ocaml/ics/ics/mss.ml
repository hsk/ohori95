(* ML-Style System λlet,# *)
open Utils
(* Syntaxs *)

type l = string
type x = string

type e =
  | ETrue
  | EFalse
  | EInt of int
  | Ex of x
  | EAbs of x * e
  | EApp of e * e
  | ERecord of (l * e) list
  | EDot of e * l
  | EModify of e * l * e
  | EVariant of l * e
  | ECase of e * (l * e) list
  | ELet of x * e * e

let rec show = function
  | ETrue             -> "true"
  | EFalse            -> "false"
  | EInt i            -> string_of_int i
  | Ex x              -> x
  | EAbs(x, e)        -> Printf.sprintf "λ%s.%s" x (show e)
  | EApp(e, e2)       -> Printf.sprintf "(%s %s)" (show e) (show e2)
  | ERecord(les)      -> Printf.sprintf "{%s}" (show_les les)
  | EDot(e, l)        -> Printf.sprintf "%s#%s" (show e) l
  | EModify(e, l, e2) -> Printf.sprintf "modify(%s,%s,%s)" (show e) l (show e2)
  | EVariant(l, e)    -> Printf.sprintf "<%s=%s>" l (show e)
  | ECase(e, les)     -> Printf.sprintf "case %s of <%s>" (show e) (show_les les)
  | ELet(x, e, e2)    -> Printf.sprintf "let %s = %s in %s" x (show e) (show e2)
and show_les les =
  String.concat "," (List.map(fun(l,e)->l^"="^show e) les)

let rec v = function
  | EInt(_) -> true
  | ETrue -> true
  | EFalse -> true
  | EAbs(x, _) -> true
  | ERecord(les) -> not (List.exists (fun (l, e) -> not (v e)) les)
  | EVariant(l, e) -> v(e)
  | _ -> false

(* Substitutions *)

let rec esub s = function
  | Ex(x) when List.mem_assoc x s -> esub s (List.assoc x s)
  | EAbs(x, e) -> EAbs(x, esub (List.del_assoc x s) e)
  | EApp(e1, e2) -> EApp(esub s e1, esub s e2)
  | ERecord(les) -> ERecord(les |> List.map(fun (l, e) -> (l, esub s e)))
  | EDot(e, l) -> EDot(esub s e, l)
  | EModify(e1, l, e2) -> EModify(esub s e1, l, esub s e2)
  | EVariant(l, e) -> EVariant(l, esub s e)
  | ECase(e, les) -> ECase(esub s e, les |> List.map (fun (l, e) -> (l, esub s e)))
  | ELet(x, e1, e2) -> ELet(x, esub s e1, esub s e2)
  | e -> e

(* Reduction rules *)

let rec eval1 = function
  | EApp(e1, e2) when not (v e1) -> EApp(eval1 e1, e2)
  | EApp(v1, e2) when not (v e2) -> EApp(v1, eval1 e2)
  | ELet(x, e1, e2) when not (v e1) -> ELet(x, eval1 e1, e2)
  | ERecord(les) ->
    let rec find hs = function
      | [] -> failwith "error"
      | (l, e) :: ls when not (v e) -> ERecord(List.rev hs @ (l, eval1 e) :: ls)
      | (l, e) :: ls -> find ((l, e) :: hs) ls
    in
    find [] les
  | EDot(e, l) when not (v e) -> EDot(eval1 e, l)
  | EModify(e1, l, e2) when not (v e1) -> EModify(eval1 e1, l, e2)
  | EModify(v1, l, e2) when not (v e2) -> EModify(v1, l, eval1 e2)
  | EVariant(l, e) when not (v e) -> EVariant(l, eval1 e)
  | ECase(e, les) when not (v e) -> ECase(eval1 e, les)

  | EApp(EAbs(x, e), v1) -> esub [x,v1] e
  | EDot(ERecord(lvs), li) -> List.assoc li lvs
  | EModify(ERecord(lvs), li, v) ->
    let rec find hs = function
      | [] -> failwith "error"
      | (l, e) :: ls when l = li -> ERecord(List.rev hs @ (l, v) :: ls)
      | (l, e) :: ls -> find ((l, e) :: hs) ls
    in
    find [] lvs
  | ECase(EVariant(l, v), ls) -> EApp(List.assoc l ls, v)
  | ELet(x, v, e) -> esub [x, v] e
  | e -> failwith "error"

let rec eval e =
  try eval (eval1 e) with _ -> e
