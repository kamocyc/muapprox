(* Random.bool () = TrueでNonTerminate *)
let rec loop () = loop ()
let succ f x = f (x + 1)
let rec app f x = if Random.bool () then app (succ f) (x - 1) else f x
let check x y = if x = y then () else loop ()
let main () =
  let n = read_int () in
  app (check n) n