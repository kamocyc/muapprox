let rec zip xs ys k =
  if xs <= 0 then k 0
  else if ys <= 0 then k 0
  else zip (xs - 1) (ys - 1) (fun r -> k (1 + r))

let () =
  let l1 = read_int () in
  let l2 = read_int () in
  zip l1 l2 (fun r -> print_int r)
  
  
(* 
(* minと同じ *)
let rec zip xs ys =
  if xs <= 0 then 0
  else let xs' = xs - 1 in
  if ys <= 0 then 0
  else let ys' = ys - 1 in 1 + zip xs' ys'

let () =
  let l1 = read_int () in
  let l2 = read_int () in
  print_int @@ zip l1 l2 *)
