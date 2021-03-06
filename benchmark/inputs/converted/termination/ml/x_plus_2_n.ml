let succ (n:int) = n + 1
let g (r : int -> int) (a : int) = r (r a)
let rec f (n : int) = if n=0 then succ else g (f (n-1))
let main () =
  let n = read_int () in
  let x = read_int () in
  if n>=0 && x>=0 then f n x else 0
