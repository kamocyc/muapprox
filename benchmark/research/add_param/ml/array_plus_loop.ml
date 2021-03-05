let make_array k = k (fun i k' -> k' 0)
let update ar i x k =
  k (fun j k' -> if j = i then k' x else ar j k')
let check ar i x k =
  ar i (fun r -> k (r = x))

let pred ar i k =
  ar i (fun x ->
    update ar i (x - 1) k
  )
  
let rec loop ar i j k =
  ar i (fun x ->
      ar j (fun y ->
        if x + y <= 0 then k 0
        else pred ar 0 (fun ar -> loop ar 0 1 k)
      )
    )

let main ar k =
  loop ar 0 1 (fun r -> k r)
    
let () =
  let x = read_int () in
  let y = read_int () in
  make_array (fun ar ->
    update ar 0 x (fun ar ->
      update ar 1 y (fun ar ->
        main ar (fun r -> print_int r)     
      )
    )
  )


  