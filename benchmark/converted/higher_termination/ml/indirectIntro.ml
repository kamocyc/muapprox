let rec app (i:int) h (v : int) (u : unit) = if i>=0 then app (i-1) h v u else (h v u : unit)
let g (u : unit) = ()
let rec f (x : int) =
  if x > 0 then
    app (Random.int 0) f (x-1)
  else
    g
let main (u:unit) = f (Random.int 0) ()
