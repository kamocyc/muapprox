let id (x:'int) k = k x
let rec omega (x:'int) (k : 'int -> 'a): 'a = omega x k
let f (x:'int -> ('int -> 'a) -> 'a) (y:'int -> ('int -> 'a) -> 'a) (z:'int) k = y z k
let rec app (h:'int -> ('int -> 'a) -> 'a) (x:'int) k = h x k

let () =
  f (app (f (app id) (app omega))) (app id) 1 (fun r -> print_int r)

(* 
(* fの第一引数は捨てられるので、結局 id 1 となる *)

let id (x:int) = x in
let rec omega (x:int) = (omega x:int) in
let f (x:int -> int) (y:int -> int) (z:int) = y z in
let rec app (h:int -> int) (x:int) = h x in
  f (app (f (app id) (app omega))) (app id) 1

 *)