(* Random.bool () = Trueで停止しない *)
let rec loop () = loop ()
let succ f x = f (x + 1)
let rec app m f x = if m > 0 then app (m - 1) (succ f) (x - 1) else f x
let check x y = if x = y then () else loop ()
let main () = app (read_int ()) (check 0) 0
