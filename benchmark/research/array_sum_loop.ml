let make_array k = k (fun i k' -> k' 0)
let update ar i x k=
  k (fun j k' -> if j = i then k' x else ar j k')
let check ar i x k =
  ar i (fun r -> k (r = x))

let rec loop n k =
  if n <= 0 then k 0
  else loop (n - 1) k

let main () k =
  let x = read_int () in
  let y = read_int () in
  make_array (fun ar ->
    update ar 0 x (fun ar ->
      update ar 1 y (fun ar ->
        ar 0 (fun x' ->
          ar 1 (fun y' ->
            loop (x' + y') k
          )
        )
      )
    )
  )

let () =
  main () (fun r -> print_int r)


  