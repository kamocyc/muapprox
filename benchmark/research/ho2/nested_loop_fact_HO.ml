
let pred f k = f (fun r -> k (r - 1))

let check f k = f (fun n -> if n <= 0 then k 0 else k 1)

let rec loop2 g k =
  check g (fun b ->
    if b = 0 then k 0
    else loop2 (pred g) k
  )

let rec mult f g k =
  f (fun fx ->
    check g (fun b ->
      if b = 0 then k 0
      else mult f (pred g) (fun r -> k (r + fx))
    )
  )
  
let rec fact acc f g k =
  check f (fun b ->
    if b = 0 then g acc k
    else fact (mult acc f) (pred f) g k
  )

let one k = k 1

let rec loop1 f k =
  fact one f loop2 (fun _ ->
    check f (fun b ->
      if b = 0 then k 0
      else loop1 (pred f) k
    )
  )

let () =
  let n = read_int () in
  loop1 (fun k -> k n) (fun r -> print_int r)

