let id (x: int) (k: int -> 'a) : 'a = k x
let rec omega (x: int) (k: int -> 'a): 'a = omega x k
let f (x:int -> (int -> 'a) -> 'a) (y:int -> (int -> 'b) -> 'b) (z:int) k = y z k
let main k =
  f (f id omega) id 1 k
  
let () =
  main (fun r -> print_int r)

(* 
let id (x:int) = x
let rec omega (x:int) = (omega x:int)
let f (x:int -> int) (y:int -> int) (z:int) = y z

let () =
  print_int @@ f (f id omega) id 1 *)
