(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let app x f = f x
let ev_a (k:unit->unit) = event "A"; k ()
let ev_b (k:unit->unit) = event "B"; k ()

let rec cont () =
  let x = read_int () in
  if x > 0 then
    app ev_a loop
  else
    app ev_b loop
and loop ev =
  ev cont

let main () = loop ev_a
