let rec app (f:int -> unit) x = f x
and down x = if x = 0 then () else down (x-1)
and up x = if x = 0 then () else up (x+1)
let main (u:unit) =
  let t1 = Random.int 0 in
  let t2 = Random.int 0 in
  if t1 > 0 then app down t1
  else if t2 < 0 then app up t2
  else ()
