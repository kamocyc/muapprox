let rec qs (cmp : int -> int -> bool) n =
  if n <= 0 then
    0
  else
    let xs' = n - 1 in
    par cmp (Random.int 0) 0 0 xs'
and  par (cmp : int -> int -> bool) x l r xs =
  if xs <= 0 then
    qs cmp l + (1 + qs cmp r)
  else
    let x' = Random.int 0 in
    let xs' = xs - 1 in
    if cmp x' x then
      par cmp x (1 + l) r xs'
    else
      par cmp x l (1 + r) xs'

let cmp (x : int) (y : int) = x >= y

let main (u:unit) =
  let n = Random.int 0 in
  qs cmp n
