(* terminate *)
let rec loop () = loop ()
let app f x = f x
let check x y = if x = y then () else loop ()
let main () =
  let a = read_int () in
  let b = read_int () in
  app (check (a <= b)) (a <= b)