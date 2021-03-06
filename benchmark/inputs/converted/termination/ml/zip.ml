let rec zip xs ys =
  if xs <= 0 then 0
  else let xs' = xs - 1 in
  if ys <= 0 then 0
  else let ys' = ys - 1 in 1 + zip xs' ys'
let main (u:unit) =
  let l1 = Random.int 0 in
  let l2 = Random.int 0 in
  zip l1 l2
