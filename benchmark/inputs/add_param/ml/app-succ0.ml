(* Random.bool () = Trueで停止しない *)
let rec loop () = loop ()
let succ f x = f (x + 1)
let rec app f x = if Random.bool () then app (succ f) (x - 1) else f x
let check x y = if x = y then () else loop ()
let main () = app (check 0) 0
