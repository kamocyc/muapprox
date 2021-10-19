(* terminate *)
let rec loop () = loop ()
let app f g = f g
let f x k = k x
let check x y = if (x = y) then () else loop ()
let main () =
  let a = read_int () in
  let b = read_int () in
  app (f (4 * a + 2 * b)) (check (4 * a + 2 * b))