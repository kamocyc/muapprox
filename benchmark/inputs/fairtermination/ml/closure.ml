let const x k = k x
let rec finish() = print_string "A"; finish()
let rec f g =
  g (fun n -> if n>0 then f (const (n-1)) else finish())
let main =
  let n = read_int () in
  f (const n)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*)

(* 
let const x () = x
let rec finish() = event "A"; finish()
let rec f g = let n = g() in if n>0 then f (const (n-1)) else finish()
let main = let n = Random.int(0) in f (const n)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*) *)