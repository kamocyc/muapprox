let rec array_max i n ar m k =
  if i >= n then
    k m
  else
    ar i (fun x ->
      (fun k2 -> if x > m then k2 x else k2 m) (fun z ->
        array_max (i + 1) n ar z k
      )
    )

let rec rand_array x i k =
  let y = read_int () in
  if y >= x + 1 then assert false else k y
  
let main n ar k =
  array_max 0 n ar (-1) k

let () =
  let n = 5 in
  let x = 10 in
  if n > 0 && x >= 0 then
    main n (rand_array x) (fun m ->
      assert (m <= x)
    )
