(* Taken from
   Koskinen and Terauchi, "Local Temporal Reasoning", CSL-LICS 2014, Figure 10 *)

let event s = print_string s

let g i x k = k (x-i)

let app f x i k =
   event "P"; (* added to capture the fact that P happened before *)
   f x (g i) k

let rec ha1 (x:int) =
   event "P"; (* added to capture the fact that P happened before *)
(*   event "Ha1";*)
   event "Ha";
   failwith "a";
   ha1 x (* added to turn "Ha1 happens" to "Ha1 happens infinitely often" *)

let rec ha2 (x:int) =
   event "P"; (* added to capture the fact that P happened before *)
(*   event "Ha2"; *)
   event "Ha";
   failwith "a";
   ha2 x (* added to turn "Ha2 happens" to "Ha2 happens infinitely often" *)

let rec walk x f k =
(*  event "Walk";*)
  event "P"; (* added to capture the fact that P happened before *)
  if x<0 then k x
  else f x (fun r -> walk r f k)

let rec run x f k =
(*  event "Run";*)
  event "P"; (* added to capture the fact that P happened before *)
  if x=0 then k x
  else f x (fun r -> print_int r; f r (fun r' -> print_int r'; run r' f k))

let rec life x =
  if read_int ()>0 then
    (event "P";
     if x<0 then app walk x (1) (fun r -> ha1 r)
     else app run x 1 (fun r -> ha2 r))
  else life x

let () = life (read_int ())

(* Property to be checked: if event P occurs infinitely often so does Ha *)
(* The original property described in their paper is
   G(P=>X (Walk U Ha1 / Run U Ha2))
   this can be expressed as the conjunction of the following properties:
    1. If P happens, then Ha1 or Ha2 happens eventually
    2. The next event after P is one of the events in {Ha1,Walk,Ha2,Run}
    3. After P and Walk happens, the next action is Walk or Ha1.
    4. After P and Run happens, the next action is Run or Ha2.
   The properties 2-4 are safety properties,
   which can be checked by plain MoCHi.
 *)
(*{SPEC}
   fairness: (Always, P)  (* either P does not happen, or *)
   fairness: (Ha, Never) (* Ha happens eventually *)
{SPEC}*)