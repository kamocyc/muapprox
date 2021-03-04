(* non-terminate *)
let rec loop_ () = loop_ ()
let myassert b = if b then () else loop_ ()

let apply f x = f x
let check x y = myassert (x = y)
let rec loop n : unit = apply (check n) n; loop (n + 1)
let main () =
  let x = read_int () in
  loop x