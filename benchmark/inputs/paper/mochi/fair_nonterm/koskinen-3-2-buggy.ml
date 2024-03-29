(*{SPEC}

  fairness: (Call, Halt)

  {SPEC}*)

let rec halt (): unit =
  event "Halt";
  halt()

let rec bar x =
  event "Call";
  if x>0 then bar (x-1)
  else x

let rec foo x =
  event "Call";
  if x<0 then foo x (*POPL16: if x<=0 then foo x *)
  else halt()

let main () =
  let t = read_int () in
  if read_int () >0 then foo 0
  else foo(bar t)
