let rec square_inner n m k =
  if m <= 0 then k 0
  else (square_inner n (m - 1) (fun r -> k (n + r)))

let square n k = square_inner n n k

let pred r k = k (r - 1)

let rec loop fn k =
  fn (fun r ->
    if r <= 0 then k 0
    else loop (pred r) k)

let () =
  let n = read_int () in
  loop (square n) (fun r -> print_int r)
