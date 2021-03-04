(* 常に Random.bool () = true の場合に停止しない *)
let rec loop () = loop ()
let rec app f x = if Random.bool () then app f (x + 1) else f x
let check x y = if x <= y then () else loop ()
let main () =
  let i = read_int () in
  app (check i) i
