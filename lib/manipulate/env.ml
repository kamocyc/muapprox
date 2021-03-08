open Hflmc2_syntax

let lookup (key : 'a Id.t) (env : ('b Id.t * 'c) list) : 'c =
  match List.find_all (fun (k, e) -> Id.eq k key) env with
  | [(_, v)] -> v
  | [] -> raise Not_found
  | _ -> failwith "multiple found"

let update bounds env = bounds @ env

let keys env =
  let rec aux acc = function
    | [] -> acc
    | (key, _) :: xs -> aux (key::acc) xs
  in
  aux [] env
  |> List.rev

let elems env =
  let rec aux acc = function
    | [] -> acc
    | (_, elem) :: xs -> aux (elem :: acc) xs
  in
  aux [] env

let entries env = env

let nth = List.nth
let length = List.length
let size = List.length

let has key env =
  try
    let _ : 'b = lookup key env in true
  with Not_found -> false

let empty = []

let create bounds = update bounds empty
