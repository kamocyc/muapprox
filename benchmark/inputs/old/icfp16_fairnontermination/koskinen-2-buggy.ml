(*{SPEC}

  fairness: (Print, Never)

  {SPEC}*)

let rec print (x:int) :unit = event "Print";print x
and rumble x y =
  if x<y then
    if read_int () >0 then
       rumble (x+1) y
    else rumble x y (*POPL16: else rumble x (y+1)*)
  else x

let main () =
  let a = read_int () in
  let b = read_int () in
    print (rumble a (rumble a b))
