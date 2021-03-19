let pred r k = k (r - 1)

let rec loop f k =
  f (fun r ->
    if r <= 0 then k 0
    else loop (pred r) k)

let () =
  (fun k ->
    let n = read_int () in
    k (fun k' -> k' n)
  ) (fun f -> loop f (fun _ -> ()))

  