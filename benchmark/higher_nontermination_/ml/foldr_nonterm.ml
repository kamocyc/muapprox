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
let rec foldr (f:int->int->int) (acc:int) (xs:int) =
  if xs = 0 then acc
  else
    let elem = read_int2 () in
    f elem (foldr f acc (xs - 1))
let rec loop (u:unit) = (loop u: int)
let rec sum_may_nonterm x y =
  let isTerminate = read_int2 () in
  if isTerminate > 0 then x+y else loop ()
let main () = 
  let xs = read_int2 () in
  if xs > 0 then
    foldr sum_may_nonterm 0 xs
  else -1
