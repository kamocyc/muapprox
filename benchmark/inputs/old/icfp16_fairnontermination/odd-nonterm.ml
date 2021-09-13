(*{SPEC}

  fairness: (A, B)

  {SPEC}*)


let rec f x =
  if x = 0 then
    ()
  else
    if read_int () > 0 then
      (event "A"; f x)
    else
      (event "B"; f (x - 2))


let main () =
  let r = read_int () in
  if r > 0 then
    f r
  else
    ()
