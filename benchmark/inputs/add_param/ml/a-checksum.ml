(* inliningしないとkatsura-solverで型が付かず、解けない *)
let rec loop () = loop ()
let myassert b = if b then () else loop ()
let make_array n = (n, fun i -> myassert (0 <= i && i < n); 0)
let update (n, ar) i x =
  myassert (0 <= i && i < n);
  (n, fun j -> if j = i then x else ar j)

let checksum (n, ar) x = myassert ((ar 0) + (ar 1) = x)
let main () = 
  let a = read_int () in
  let b = read_int () in
  checksum (update (update (make_array 2) 0 a) 1 b) (a + b)