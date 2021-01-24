let rec eventA _ = print_string "A"; f 1
and f x =
  if x < 0 then ()
  else if x = 0 then eventA "A"
  else f 0

let () =
  let n = read_int () in
  if n = 0 then print_string "A" (* event "A" *)
  else f n

(* 
let rec f x =
  if x < 0 then ()
  else if x = 0 then (event "A")
  else (f 0; f 1)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*) *)