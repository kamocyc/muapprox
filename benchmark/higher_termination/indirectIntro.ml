let rec app (i:int) h (v : int) (u : unit) k = if i>=0 then app (i-1) h v u k else (h v u k : unit)
let g (u : unit) k = k ()
let rec f (x : int) y k =
  if x > 0 then
    app (read_int()) f (x-1) y k
  else
    g y k
  
let () =
  f (read_int ()) () (fun r -> ())

(* 
let rec app (i:int) h (v : int) (u : unit) = if i>=0 then app (i-1) h v u else (h v u : unit)
let g (u : unit) = ()
let rec f (x : int) y =
  if x > 0 then
    app (read_int()) f (x-1) y
  else
    g y
let () =
  f (read_int ()) () *)
