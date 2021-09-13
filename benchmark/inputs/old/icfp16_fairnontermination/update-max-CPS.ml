(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let ev_a (k:unit->unit) = event "A"; k ()
let ev_b (k:unit->unit) = event "B"; k ()

let rec cont x () =
  let y = read_int () in
  if x < y then
    update_max_CPS ev_b y
  else
    update_max_CPS ev_a x
and update_max_CPS ev x =
  ev (cont x)

let main () =
  let x = read_int () in
  update_max_CPS ev_a x
