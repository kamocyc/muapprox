let isPositive (n:int) = n > 0
let isNegative (n:int) = n < 0
let rec f (cond:int->bool) (x:int) =
  if cond x then f cond (x - 1) else ()
let main () =
  let r = read_int () in
  let n = read_int () in
  if r > 0 then f isPositive n
           else f isNegative n
