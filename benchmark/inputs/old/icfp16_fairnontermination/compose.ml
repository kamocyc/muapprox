(*{SPEC}

  fairness: (A, B)

  {SPEC}*)

let pred x = x - 1
let compose f g x = f (g x)

let rec f c =
  event "A";
  if c = 0 then
    ()
  else
    (event "B";
     compose f pred c)

let main () =
  let r = read_int () in
  f r
