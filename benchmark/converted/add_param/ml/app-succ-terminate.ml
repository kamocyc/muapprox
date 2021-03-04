(* Random.bool () = TrueでNonTerminate *)
let rec loop () = loop ()
let succ f x = f (x + 1)
let rec app m f x = if m > 0 then app (m - 1) (succ f) (x - 1) else f x
let check x y = if x = y then () else loop ()
let main () =
  let n = read_int () in
  let m = read_int () in
  app m (check n) n
