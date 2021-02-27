(* 
Sentry =u ∀n. Main (\k. k n).
Main f =u
  f (\n.
    (n > 0 => Main (n - 1) (\k. k (n - 1))) /\ (n <= 0 => true)
  ).
*)

let c = ref 0

let rec main f g =
  f (g (fun n ->
    c := !c + 1;
    (if n > 0 then main (fun k -> k (n - 1)) (fun k -> fun m -> k m)
    else ())
  ))

let () =
  let n = read_int () in
  main (fun k -> k (n * n)) (fun k -> fun m -> k (m * m));
  print_int (!c)

(* let rec main n =
  if n () > 0 then (
    (* print_int @@ ((fun () -> n () - 1) ()); *)
    main (fun () -> n () - 1)
  ) else
    ()

let () =
  let n = read_int () in
  main (fun () -> n) *)
  
(*  

(* 1階バージョン *)
let rec main n =
  if n > 0 then
    main (n - 1)
  else
    ()

let () =
  let n = read_int () in
  main n
  
   *)