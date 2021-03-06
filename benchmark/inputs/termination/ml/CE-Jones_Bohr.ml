(* idが返る *)
let f1 (u:bool) (c:int->int) (d:int) = d
let f2 (u:bool) (a:((int -> int) -> int -> int) -> int -> int) (b:int->int) x = a (f1 u) x
let f3 (u:bool) (a:((int -> int) -> int -> int) -> int -> int) x = a (f2 u a) x
let f4 (u:bool) (v:int) = v
let f5 (u:bool) (e:(int->int)->(int->int)) (x:int) = e (f4 u) x
let () =
  let zz_1032 = f3 false (f5 false) in
  print_int (zz_1032 10)
 