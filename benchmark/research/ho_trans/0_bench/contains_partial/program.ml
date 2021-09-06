let check f k =
  f (fun n ->
    if n <= 0 then k 0 else k 1
  )

let pred f k =
  f (fun r -> k (r - 1))

let rec loop2 h k =
  check h (fun b ->
    if b = 0 then k false else loop2 (pred h) k
  )
  
let rec loop g h k =
  check g (fun b ->
    if b = 0 then loop2 h k else loop (pred g) h k
  )
  
let m g h =
  loop g h (fun _ -> ()); loop h g (fun _ -> ())

let a f =
  let y = read_int () in
  f (fun k -> k y)

let () =
  let x = read_int () in
  a (m (fun k -> k x))
