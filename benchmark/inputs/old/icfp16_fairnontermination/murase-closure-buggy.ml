(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let const x () = x
let rec finish() = event "A"; finish()

let rec f g =
  let n = g() in
  if n>0 then
    f (const (n)) (*POPL16: f (const (n-1)) *)
  else finish()

let main () =
  let n = read_int () in
  f (const n)
