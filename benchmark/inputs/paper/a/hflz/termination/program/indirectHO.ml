let id (x:unit) = x
let app (h:unit -> unit -> unit) v = h () v
let rec f n u =
  if n > 0 then
    app (f (n-1))
  else
    id
let main (u:unit) = f (Random.int 0) () ()
