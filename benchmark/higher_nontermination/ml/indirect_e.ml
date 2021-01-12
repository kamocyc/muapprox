let app f (x:int) k = f x k
let id (u:unit) = u
let rec g (x:int) k =
  if x=0 then k id else app g (x-1) k
let main () =
  let t = read_int () in g t (fun f -> f ())