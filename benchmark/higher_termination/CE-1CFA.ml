let id (x:'int) k = k x
let rec omega (x:'int) (k : 'int -> 'a): 'a = omega x k
let f (x:'int -> ('int -> 'a) -> 'a) (y:'int -> ('int -> 'a) -> 'a) (z:'int) k = y z k
let rec app (h:'int -> ('int -> 'a) -> 'a) (x:'int) k = h x k

let () =
  f (app (f (app id) (app omega))) (app id) 1 (fun r -> print_int r)
