(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let succ x = x + 1

let rec op_loop op =
  let x = read_int () in
  let y = op x in
  if y > 0 then
    (event "A";
     op_loop succ)
  else
    (event "B";
     op_loop succ)

let main () = op_loop succ
