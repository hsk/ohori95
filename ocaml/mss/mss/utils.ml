module List = struct
  include List
  let rec del_assoc x = function
    | [] -> []
    | (x1,_)::ls when x = x1 -> del_assoc x ls
    | l::ls -> l::del_assoc x ls
  let rec del x = function
    | [] -> []
    | x1::ls when x = x1 -> del x ls
    | l::ls -> l::del x ls
  let rec union s1 = function
    | [] -> s1
    | x::xs when List.mem x s1 -> union s1 xs
    | x::xs -> union (s1@[x]) xs
  let rec union_assoc (s1:('a * 'b) list):('a * 'b) list -> ('a * 'b) list = function
    | [] -> s1
    | (l,x)::xs when List.mem_assoc l s1 -> union s1 xs
    | x::xs -> union (s1@[x]) xs
  let rec inter s1 s2 = match s1 with
    | [] -> []
    | x::xs when List.mem x s2 -> x::inter xs s2
    | _::xs -> inter xs s2
  let rec delete ys = function
    | [] -> []
    | x::ls when List.mem x ys -> delete ys ls
    | l::ls -> l::delete ys ls
  let rec delete_assoc ys = function
    | [] -> []
    | (l,x)::ls when List.mem l ys -> delete_assoc ys ls
    | l::ls -> l::delete_assoc ys ls
  let keys ls = List.map fst ls
end

module MMake(Ord : Map.OrderedType) = struct
  include Map.Make(Ord)
  let of_list ls =
    List.fold_left (fun m (k,v) -> add k v m) empty ls
  let rec union a b = merge (fun key a b ->
    match a,b with
    | _,Some(b) -> Some(b)
    | Some(a),_ -> Some(a)
    | _ -> None ) a b
  let keys l = l |> bindings |> List.map(fun(k,_)->k)
  let diff xs ys = fold(fun k a b -> remove k b) ys xs
  let add_list xs m = List.fold_left (fun m (k,v) -> add k v m) m xs
end
module M = MMake(String)
module S = struct
  include Set.Make(String)
  let of_list ls =
    List.fold_left (fun s v -> add v s) empty ls
end
