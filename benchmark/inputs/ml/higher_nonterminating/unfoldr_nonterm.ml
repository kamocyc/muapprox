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
let rec unfoldr_sum (f:int->bool*int*int) (seed:int) =
  let (isEnd, elem, next_seed) = f seed in
  if isEnd then 0
  else elem + unfoldr_sum f next_seed
let pred n = if n=0 then (false, 0, 0) else (true, 1, n-1)
let main () =
  let r = read_int2 () in
  unfoldr_sum pred r
