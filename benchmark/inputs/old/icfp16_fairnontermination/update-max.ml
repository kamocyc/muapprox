(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let rec update_max x =
  let y = read_int () in
  if x < y then
    (event "B";
     update_max y)
  else
    (event "A";
     update_max x)

let main () =
  let x = read_int () in
  update_max x
