let app (h:unit -> unit -> unit) (v:unit) = (h () v : unit)
let id (u:unit) = u
let rec g (x:int) (u:unit) =
  if x = 0 then id else app (g (x-1))
let main () =
  let r = read_int () in
  g r () ()
