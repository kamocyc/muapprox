(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let app_unit f = f ()

let rec loop () =
  let x = read_int () in
  if x > 0 then
    (event "A";
     app_unit loop)
  else
    (event "B";
     app_unit loop)

let main () = loop ()
