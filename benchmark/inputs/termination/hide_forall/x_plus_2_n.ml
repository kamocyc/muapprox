
let check nf xf k =
  nf (fun n -> xf (fun x ->
    if n >= 0 && x >= 0 then k 1
    else k 0
  ))
let g r a k = r a (fun r' -> r (fun k -> k r') k)
let succ n k = k (n + 1)
let rec f nf mf k =
  nf (fun n -> mf (fun (m: int) ->
    if n = 0 then succ m k else g (f (fun k -> k (n - 1))) (fun k -> k m) k
  ))

let main k =
  (fun kf -> kf (fun kn -> kn (read_int ())) (fun kx -> kx (read_int ())))
  (fun nf xf -> (check nf xf (fun b -> if b = 1 then f nf xf k else k 0)))
  
let () = main (fun r -> ())