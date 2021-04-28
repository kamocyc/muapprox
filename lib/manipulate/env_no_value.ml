open Hflmc2_syntax

type 'a elt = 'a Id.t
type 'a t = 'a elt list

(* https://stackoverflow.com/a/30634912/12976091 *)
let cons_uniq f xs x = if List.exists (f x) xs then xs else x :: xs
let remove_from_left f xs = List.rev (List.fold_left (cons_uniq f) [] xs)
let remove_dublicate (env : 'a t) = remove_from_left (Id.eq) env
let exists_duplication ids =
  List.length ids <> (List.length @@ remove_dublicate ids)
  
let lookup (key : 'b Id.t) (env : 'a t) : 'a Id.t =
  match List.find_all (fun e -> Id.eq e key) env with
  | [e] -> e
  | [] -> raise Not_found
  | _ -> failwith "multiple found"

let update (bounds : 'a Id.t list) (env : 'a t) : 'a t =
  if exists_duplication bounds then failwith "update duplicate 1";
  if exists_duplication env then failwith "update duplicate 2";
  let env' = List.filter (fun e -> not @@ List.exists (fun b -> Id.eq b e) bounds) env in
  bounds @ env'

let empty = []

let create bounds = update bounds empty

let remove (bounds : 'a Id.t list) (env : 'a t) : 'a t =
  List.filter (fun e -> not @@ List.exists (fun b -> Id.eq b e) bounds) env

let merge (envs : 'a t list) =
  envs |> List.flatten |> remove_dublicate
let to_list x = x
