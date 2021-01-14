let compose (f : int -> (int -> 'a) -> 'a) (g : int -> (int -> 'a) -> 'a) x k = g x (fun r -> f r k)
let id (x : int) k = k x
let succ x k = k (x + 1)
let rec toChurch n f x k =
  if n = 0 then id x k else compose f (toChurch (n - 1) f) x k

let () =
  let x = read_int () in
  if x >= 0 then
    let tos = toChurch x succ in
    tos 0 (fun r -> print_int r)
  else ()

(* 
let compose (f : int -> int) (g : int -> int) x = f (g x)
let id (x : int) = x
let succ x = x + 1
let rec toChurch n f =
  if n = 0 then id else compose f (toChurch (n - 1) f)
let () = 
  let x = read_int ()in
  if x>=0 then
    let tos = toChurch x succ in print_int (tos 0)
  else () *)
