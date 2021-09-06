let check f k =
  f (fun n ->
    if n <= 0 then k 0 else k 1
  )
  
let pred f k =
  f (fun r -> k (r - 1))
  
let add f g k =
  f (fun fx -> g (fun gx -> k (fx  + gx)))

let rec mult acc f g k =
  check f (fun b ->
    if b = 0 then k acc else mult (add acc g) (pred f) g k
  )
  
let rec loop k g =
  check g (fun b ->
    if b = 0 then k 0 else loop k (pred g)
  )
  
let () =
  let n = read_int () in
  mult
    (fun k -> k 0)
    (fun k -> k n)
    (fun k -> k n)
    (fun g ->
      loop (fun r -> ()) g
    )
    
