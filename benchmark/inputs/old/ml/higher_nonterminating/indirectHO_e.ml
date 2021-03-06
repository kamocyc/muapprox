let read_int2 () =
  let res = read_int () in
  if res <= (-3) then
    -3
  else if res <= 0 then
    0
  else if res <= 1 then
    1
  else if res <= 3 then
    3
  else
    10
let app (h:unit -> unit -> unit) (v:unit) = (h () v : unit)
let id (u:unit) = u
let rec g (x:int) (u:unit) =
  if x = 0 then id else app (g (x-1))
let main () =
  let r = read_int2 () in
  g r () ()
