let app f (x:int) (u:unit) = (f x u: unit)
let id (u:unit) = u
let rec g (x:int) =
  if x=0 then id else app g (x-1)
let main () =
  let t = read_int () in g t ()
