(*{SPEC}

  fairness: (A, B)

  valcegar #randint_1:
  (x_2:int[x_2=1; x_2<=-1] -> (r:int[r>0] -> X) -> X)

  valcegar #randint_2:
  (unit -> unit -> (x_4:int[1 = x_4] -> X) -> X)

  valcegar f :
  (x_2:int[1 <= -x_2; 1 = x_2] -> (unit -> X) -> X)

{SPEC}*)


let rec f x =
  if x = 0 then
    ()
  else
    if read_int () > 0 then
      (event "A"; f x)
    else
      (event "B"; f (x - 2))

let main () =
  let r = read_int () in
  if r > 0 then
    f r
  else
    ()
