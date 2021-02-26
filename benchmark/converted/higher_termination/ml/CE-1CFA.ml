let id (x:int) = x
let rec omega (x:int) = (omega x:int)
let f (x:int -> int) (y:int -> int) (z:int) = y z
let rec app (h:int -> int) (x:int) = h x
let main () =
  f (app (f (app id) (app omega))) (app id) 1

