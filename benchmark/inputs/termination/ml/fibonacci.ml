let rec fib n k =
  if n < 2 then k 1
  else fib (n - 1) (fun r -> fib (n - 2) (fun r' -> k (r + r')))
  
let () =
  let n = read_int () in
  fib n (fun r -> print_int r)
  
(* let rec fib n =
  if n < 2 then 1
  else fib (n -1) + fib (n-2)
  
let main (u : unit) =  fib (Random.int 0) *)
