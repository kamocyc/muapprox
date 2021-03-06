let rec foldr (h : int -> int -> int) (e : int) (l : int) =
  if l = 0 then e
           else h (Random.int 0) (foldr h e (l-1))
let sum m n = m + n
let main (u:unit) =
  let l = Random.int 0 in
  if l >= 0 then
    foldr sum (Random.int 0) l
  else 0
