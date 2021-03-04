(* 常に Random.bool () = true の場合に停止しない *)
let rec loop () = loop ()
let rec app m f x = if m > 0 then app (m - 1) f (x + 1) else f x
let check x y = if x <= y then () else loop ()
let main () =
  let i = read_int () in
  let m = read_int () in
  app m (check i) i
