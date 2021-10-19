(* Taken from Example 2 of
   Hofmann and Chen, "Buchi Types for Infinite Traces and Liveness", CSL-LICS 2014 *)
let rec inner_loop i s =
  if i<1024 && not(s=0) then
    let s = Random.int(0) in
      inner_loop (i+1) s
  else event "C"
let rec loop () =
   inner_loop 0 0; event "B"; loop()
let main () = loop()


(* Property to be checked: "if C occurs infinitely often, so does B"
  *)
(*{SPEC}
   fairness: (B, Never)
   fairness: (Always, C)
{SPEC}*)