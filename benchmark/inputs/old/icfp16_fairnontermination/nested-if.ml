(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let ev_a _ = event "A"; ()
let ev_b _ = event "B"; ()

let rec f ev =
  ev ();
  let x = read_int () in
  let y = read_int () in
  if x < y then
    if x > y + 1 then
      ()
    else
      f ev_b
  else
    f ev_a

let main () = f ev_a
