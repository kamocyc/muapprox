let read_int2 () =
  let res = read_int () in
  if res <= (-3) then
    -3
  else if res <= 0 then
    0
  else if res <= 1 then
    1
  else if res <= 3 then
    3
  else
    10
let is_zero n = n = 0
let succ_app (f:int->bool) n = f (n + 1)
let rec f n (cond:int->bool) =
  if cond n then
    ()
  else
    f n (succ_app cond)
let main () = let r = read_int2 () in f r is_zero
