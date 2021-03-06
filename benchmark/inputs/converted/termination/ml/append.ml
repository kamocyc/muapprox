let rec append xs ys =
  if xs <= 0 then ys
  else let xs' = xs - 1 in 1 + append xs' ys
let main (u:unit) =
  let l1 = Random.int 0 in  
  let l2 = Random.int 0 in
  append l1 l2
