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
let isPositive (n:int) = n > 0
let isNegative (n:int) = n < 0
let rec f (cond:int->bool) (x:int) =
  if cond x then f cond (x - 1) else ()
let main () =
  let r = read_int2 () in
  let n = read_int2 () in
  if r > 0 then f isPositive n
           else f isNegative n
