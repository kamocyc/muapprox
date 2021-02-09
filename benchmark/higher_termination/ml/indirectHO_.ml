let app h v = h () v
let id x = x
let rec g x u =
  if x <= 0 then id else app (g (x-1))
let main () =
  let n = read_int () in
  g n () ()

let () = main ()

(* 
Main =u ∀n. G n false false (\_. true).
G x u k =u (x <= 0 => Id) /\ (x > 0 => App (g (x-1))).
Id x =u x.
App h v =u h false v.
 *)