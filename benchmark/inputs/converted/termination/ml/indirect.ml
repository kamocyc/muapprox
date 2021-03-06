let id (x:unit) = x
let app h (v : int) (u : unit) = (h v u : unit)
let rec f (x : int) =
  if x > 0 then
    app f (x-1)
  else
    id
let main (u:unit) = f (Random.int 0) ()
