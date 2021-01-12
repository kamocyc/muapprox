let succ (n:int) k = k (n + 1)
let g (r : int -> (int -> 'a) -> 'a) (a : int) k = r a (fun r' -> r r' k)
let rec f (n : int) m k =
  if n=0 then succ m k
  else g (f (n-1)) m k
let main (n:int) (x:int) k =
  if n>=0 && x>=0 then f n x k else k 0

(* 
(* main n m = 2^n + m *)
let succ (n:int) = n + 1
let g (r : int -> int) (a : int) = r (r a)
let rec f (n : int) = if n=0 then succ else g (f (n-1))
let main (n:int) (x:int) = if n>=0 && x>=0 then f n x else 0

let () =
  main 20 20 |> print_int *)

