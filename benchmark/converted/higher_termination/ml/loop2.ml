let rec f m n =
  let r = Random.int 0 in
  if r > 0 && m > 0 then f (m-1) n
  else if r <= 0 && n > 0 then f m (n-1)
  else ()
let main (u:unit) = f (Random.int 0) (Random.int 0)
