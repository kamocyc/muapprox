(* 方が合わない... *)
let rec succ (m:('a->('a->'b)->'b)->'a->('a->'b)->'b) (s:'a->('a->'b)->'b) (z:'a) (k:'a->'b):'b = s z (fun r -> m s r k)
let rec id (x:'a) (k:'a->'b):'b = k x
let rec two (f:'a->('a->'b)->'b) (z:'a) (k:'a->'b):'b = f z (fun r -> f r k)
let rec zero (f:'a->('a->'b)->'b) (z:'a) (k:'a->'b):'b = k z
(* f z = ('a->'b)->'b *)
let main () = two succ zero id

let () = print_int @@ main ()

(* 
let rec succ m s z = m s (s z)
let rec id x = x
let rec two f z = f (f z)
let rec zero f z = z
let main (u:unit) = two succ zero id 0

let () = print_int @@ main () *)
