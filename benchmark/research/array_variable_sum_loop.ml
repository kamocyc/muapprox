let make_array k = k (fun i k' -> k' 0)
let update ar i x k=
  k (fun j k' -> if j = i then k' x else ar j k')
let check ar i x k =
  ar i (fun r -> k (r = x))

let rec loop n k =
  if n <= 0 then k 0
  else loop (n - 1) k

let rec set ar n k = 
  if n <= 0 then
    k ar
  else
    update ar n n (fun ar -> set ar (n - 1) k)

let rec sum ar n k =
  if n = 0 then
    k 0
  else
    ar n (fun e ->
      sum ar (n - 1) (fun r -> k (r + e)) 
    )
    
let main () k =
  let n = read_int () in  
  make_array (fun ar ->
    set ar n (fun ar ->
      sum ar n (fun r -> loop r (fun _ -> ()))
    )
  )

let () =
  main () (fun r -> print_int r)


  