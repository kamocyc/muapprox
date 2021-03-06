let app f x k = f x k
let rec down x k = if x = 0 then k () else down (x-1) k
let rec up x k = if x = 0 then k () else up (x+1) k

let main k =
  let t1 = read_int() in
  let t2 = read_int() in
  if t1 > 0 then app down t1 k
  else if t2 < 0 then app up t2 k
  else k ()

let () = main (fun r -> ())
  

(* 
let rec app (f:int -> unit) x = f x
and down x = if x = 0 then () else down (x-1)
and up x = if x = 0 then () else up (x+1)
let () =
  let t1 = read_int() in
  let t2 = read_int() in
  if t1 > 0 then app down t1
  else if t2 < 0 then app up t2
  else ()
   *)
