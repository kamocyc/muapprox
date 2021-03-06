let pred x k = k (x - 1)
let succ x k = k (x + 1)

let rec down fx k =
  fx (fun x ->
    if x = 0 then k false else down (pred x) k
  )
let rec up fx k =
  fx (fun x ->
    if x = 0 then k false else up (succ x) k
  )
let app f fx k = f fx k

let check f1 f2 k =
  f1 (fun t1 -> f2 (fun t2 -> if t1 > 0 then k 0 else if t2 < 0 then k 1 else k 2))

let main k =
  (fun k3 ->
    k3
      (fun k2 -> 
        let t1 = read_int () in
        k2 t1)
      (fun k4 ->
        let t2 = read_int () in
        k4 t2
      )
  )
  (fun f1 f2  ->
    check f1 f2 (fun b ->
      if b = 0 then app down f1 k
      else if b = 1 then app up f2 k
      else k false
    )
  )
  
let () = main (fun r -> ())
