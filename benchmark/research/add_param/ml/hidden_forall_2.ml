(* hidden_forallを、loopの中でnが現れないようにした。本質的にはhidden_forallと変わらない *)
let pred f k = f (fun x -> k (x - 1))
let check f k = f (fun x -> if x <= 0 then k 1 else k 0)
let rec loop f k =
  check f (fun b ->
    if b = 1 then k 0
    else loop (pred f) k
  )

let () =
  (fun k ->
    let n = read_int () in
    k (fun k' -> k' n)
  ) (fun f -> loop f (fun _ -> ()))
