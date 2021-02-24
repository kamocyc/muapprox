let hd len l k = l 0 k
let tl len l k = k (len - 1) (fun i k -> l (i + 1) k)
let is_nil len l k = if len = 0 then k 1 else k 0

let rec for_all (f: int -> bool) len l k =
  is_nil len l (fun b -> 
    if b = 1 then
      k true
    else
      hd len l (fun e ->
        tl len l (fun len' xs' ->
          for_all f len' xs' (fun b' ->
            k (b' && f e)
          )
        )
      )
  )

let main len k =
  for_all
    (fun x -> x <= len)
    len (fun i k -> k (len - i))
    k

let () =
  main 10 (fun r ->
    print_string @@ string_of_bool r
  )
