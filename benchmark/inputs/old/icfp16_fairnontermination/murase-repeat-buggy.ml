(*{SPEC}

  fairness: (A, Never)

  {SPEC}*)

let rec repeat g =
  g (read_int ());
  repeat g

let rec f x =
  if x>0 then
    f x (*POPL16: f (x-1) *)
  else
    (event "A";())

let main () = repeat f
