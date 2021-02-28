(* fact n 回ループをする *)
let pred r k = k (r - 1)

let rec mult n m k =
  if m <= 0 then k 0
  else mult n (m - 1) (fun r -> k (n + r))

let rec fact n k =
  if n <= 0 then k 1
  else fact (n - 1) (fun r -> mult n r k)

let rec loop f k =
  f (fun n ->
    if n <= 0 then k 0
    else loop (pred n) k
  )
  
let () =
  let n = read_int () in
  loop (fact n) (fun r -> print_int r
)