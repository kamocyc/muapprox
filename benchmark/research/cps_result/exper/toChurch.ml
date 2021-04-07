(* let compose (f : int -> (int -> 'a) -> 'a) (g : int -> (int -> 'a) -> 'a) x k = g x (fun r -> f r k) *)
let compose f g x = f (g x)
let id x = x
let succ x = (x + 1)
let rec toChurch n f x =
  if n = 0 then id x else compose f (toChurch (n - 1) f) x

let pred (n : ('a -> 'a) -> 'a -> 'a) f x = n (fun g -> fun h -> h (g f)) (fun u -> x) (fun u -> u)

let f_true a b = a
let f_false a b = b

let iszero (n : ('a -> 'a) -> 'a -> 'a) = n (fun x -> f_false) f_true

let rec loop : 'a. (((('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> 'a -> 'a -> 'a) ->
  ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> 'a -> 'a -> 'a) ->
 (('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> 'a -> 'a -> 'a) ->
 ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> 'a -> 'a -> 'a) ->
'a -> 'a -> 'a = fun cn ->
  iszero cn (fun f z -> z) (loop (pred cn))

let to_int cn =
  cn ((+)1) 0

let main () =
  let n = read_int () in
  let cn = toChurch n in
  let cn = pred cn in
  let n = to_int cn in
  print_int n
  (* loop cn *)

let () = main ()
