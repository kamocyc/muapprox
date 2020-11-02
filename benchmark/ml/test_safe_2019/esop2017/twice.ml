let rec mult n m =
  if m = 0 then
    0
  else if m < 0 then
    - n + mult n (m+1)
  else
    n + mult n (m-1)
let main n m =
let twice f x = f (f x)
in if n < 0 && m > 0 then assert (0 <= twice (mult n) m)
