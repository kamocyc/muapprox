let id x = x
let app (h : unit -> 'a -> ('b -> 'c) -> 'c) (v : 'a) (k: 'b -> 'c) = h () v k
let rec f n u x k =
  if n > 0 then
    app (f (n-1)) x k
  else
    k (id x)
  
let () =
  f (read_int ()) () () (fun r -> ())

(* 
let id (x:unit) = x
let app (h:unit -> unit -> unit) v = h () v
let rec f n u x =
  if n > 0 then
    app (f (n-1)) x
  else
    id x
  
let () =
  f (read_int ()) () () *)
