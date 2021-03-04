(* terminate *)
let rec loop () = loop ()
let myassert b = if b then () else loop ()
let make_array n = (n, fun i -> myassert (0 <= i && i < n); 0)
let update (n, ar) i x =
  myassert (0 <= i && i < n);
  (n, fun j -> if j = i then x else ar j)

let check (n, ar) i x = myassert (ar i = x)
let main () =
  let n = read_int () in
  let i = read_int () in
  let x = read_int () in
  if 0 <= i && i < n then
    check (update (make_array n) i x) i x