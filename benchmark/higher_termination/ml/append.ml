
let rec append xs ys k =
  if xs <= 0 then k ys
  else let xs' = xs - 1 in append xs' ys (fun r -> k (1 + r))
  
let () =
  let l1 = read_int () in
  let l2 = read_int () in
  append l1 l2 (fun r -> print_int r)
  
(* 
(* (+)と同じ *)
let rec append xs ys =
  if xs <= 0 then ys
  else let xs' = xs - 1 in 1 + append xs' ys
  
let () =
  let l1 = read_int () in
  let l2 = read_int () in
  print_int @@ append l1 l2 *)
