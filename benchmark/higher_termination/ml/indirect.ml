let id x = x

(* CPSの関数を呼び出し *)
let app (h : 'a -> 'b -> ('c -> 'd) -> 'd) (v : 'a) (u : 'b) (k : 'c -> 'd) : 'd = (h v u k)

let rec f x (y: unit) k =
  if x > 0 then
    app f (x-1) y k
  else
    k (id y)
    
let () = f (read_int()) () (fun r -> ())

(* 
(* unit -> unit *)
let id (x:unit) = x
let app h (v : int) (u : unit) = (h v u : unit)
let rec f (x : int) y =
  if x > 0 then
    app f (x-1) y
  else
    id y
let () = f (read_int()) () *)
