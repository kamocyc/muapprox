let is_zero n = n = 0
let succ_app (f:int->bool) n = f (n + 1)
let rec f n (cond:int->bool) =
  if cond n then
    ()
  else
    f n (succ_app cond)
let main () = let r = read_int () in f r is_zero
