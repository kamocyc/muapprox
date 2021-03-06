(* n^2回ループするので、n^2の結果を渡す必要 *)
(* loopの中で直接n^2が現れない *)
let rec mult n m k =
  if m <= 0 then k 0
  else mult n (m - 1) (fun r -> k (n + r))
  
let pred f k = f (fun r -> k (r - 1))

let check f k = f (fun n -> if n <= 0 then k 0 else k 1)

let rec loop f k =
  check f (fun b ->
    if b = 0 then k 0
    else loop (pred f) k)

let () =
  let n = read_int () in
  loop (mult n n) (fun _ -> ())
