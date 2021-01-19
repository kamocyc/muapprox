(* Taken from Example 2 of
   Hofmann and Chen, "Buchi Types for Infinite Traces and Liveness", CSL-LICS 2014 *)
let event s = print_string s
let rec inner_loop i s =
  if i<1024 && not(s=0) then
    let s = read_int () in
      inner_loop (i+1) s
  else event "C"
let rec loop () =
   inner_loop 0 0; event "B"; loop()
let main () = loop()

let () = main ()

(* Property to be checked: "if C occurs infinitely often, so does B"
  *)
(*{SPEC}
   fairness: (B, Never)
   fairness: (Always, C)
{SPEC}*)