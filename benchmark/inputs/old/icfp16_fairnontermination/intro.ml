(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let rand () =
  let r = read_int () in
  if 0 <= r then
    (event "B"; r)
  else
    (event "A"; r)

let rec randpos () =
  let x = rand () in
  if 0 < x then
    x
  else
    randpos ()

let main () = randpos ()
