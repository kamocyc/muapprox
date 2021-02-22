let make_array k = k (fun i k' -> k' 0)
let update ar i x k=
  k (fun j k' -> if j = i then k' x else ar j k')
let check ar i x k =
  ar i (fun r -> k (r = x))

let main () k =
  let i, x = 2, 5 in
  make_array (fun ar ->
    update ar i x (fun ar ->
      check ar (i - 1) x k
    )
  )

let () =
  main () (fun r -> print_endline @@ string_of_bool r)

  