(* terminate *)
let rec loop () = loop ()
let myassert b = if b then () else loop ()
let apply f x = f x
let check x y = myassert (x = y)
let main () =
  let n = read_int () in
  apply (check n) n
