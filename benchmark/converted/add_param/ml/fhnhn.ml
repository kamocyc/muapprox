let rec loop () = loop ()
let f x y = if (x () = y ()) then () else loop ()
let h (x:int) u = x
let main () =
  let n = read_int () in
  f (h n) (h n)