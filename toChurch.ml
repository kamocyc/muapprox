(* let compose (f : int -> (int -> 'a) -> 'a) (g : int -> (int -> 'a) -> 'a) x k = g x (fun r -> f r k) *)
let compose f g x k = g x (fun r -> f r k)
(* let id (x : int) k = k x *)
let id x k = k x
let succ x k = k (x + 1)
let rec toChurch n f x k =
  if n = 0 then id x k else compose f (toChurch (n - 1) f) x k

let pred n f x = n (fun g -> fun h -> h (g f)) (fun u -> x) (fun u -> u)

let f_true a b = a
let f_false a b = b

let iszero n = n (fun x -> f_false) f_true

let rec loop cn =
  (* let p = pred cn in *)
  iszero cn (fun f z -> z) (loop (cn))

let () =
  let n = read_int () in
  let cn = toChurch n in
  loop cn
  