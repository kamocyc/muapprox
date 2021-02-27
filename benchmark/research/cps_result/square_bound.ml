let rec mult n m k =
  if m <= 0 then k 0
  else mult n (m - 1) (fun r -> k (n + r))
  
let pred r k = k (r - 1)

let rec loop f k =
  f (fun r ->
    if r <= 0 then k 0
    else loop (pred r) k)

let () =
  let n = read_int () in
  loop (mult n n) (fun _ -> ())
