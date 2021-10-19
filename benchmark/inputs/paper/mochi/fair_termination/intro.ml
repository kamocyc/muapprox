let rec f x =
  if x < 0 then ()
  else if x = 0 then (event "A")
  else (f 0; f 1)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*)
