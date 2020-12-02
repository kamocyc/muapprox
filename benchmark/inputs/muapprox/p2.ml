
(* これをrefinement typeつけてconvertするのは、non-trivial *)
(* というか別に任意の性質はいらないので、must-not-reachbility = not (may-reachbility) でいける *)

(*

S =v ∀i. App i (Check i).
App x f =u App (x + 1) f \/ f x.
(* equivalent to Check x y = x > y. *)
Check x y =u (x > y \/ false) /\ (x <= y \/ true).


*)

let rec app x f =
  let n = read_int () in
  if n = 0 then app (x + 1) f
  else f x

let check x y =
  if x <= y then ()
  else (failwith "fail")

let main i =
  app i (check i)

let () =
  let m = read_int () in
  main m