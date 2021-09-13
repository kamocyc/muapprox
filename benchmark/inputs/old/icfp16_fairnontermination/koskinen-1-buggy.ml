(*{SPEC}

  fairness: (Done, Never)

  {SPEC}*)


let rec finish ():unit = event "Done";finish()
and reduce x r =
  if x<=0 then x else r x

let rec explore x r =
  let y = reduce x r in
  if y=0 then finish() (*POPL16: if y<=0 then finish() *)
  else explore y r

let f x = x-2

let main () =
  let t = read_int () in
  explore t f
