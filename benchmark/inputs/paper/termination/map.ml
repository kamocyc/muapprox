let rec map f xs =
  if xs = 0 then 0
  else f (Random.int 0) + map f (xs - 1)
let compose (f : int -> int) (g : int -> int) x = f (g x)
let add x y = x + y
let main (u:unit) =
  let l = Random.int 0 in
  if l >= 0 then map (compose (add 1) (add 2)) l
            else 0
