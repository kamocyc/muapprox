let id (x:int) = x
let rec omega (x:int) = (omega x:int)
let f (x:int -> int) (y:int -> int) (z:int) = y z
let main () =
  f (f id omega) id 1

