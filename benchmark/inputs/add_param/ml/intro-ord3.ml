(* Random.bool() = trueだと停止しない *)
let rec loop () = loop ()
let succ f x = f (x + 1)
let rec app3 f g = if Random.bool () then app3 (succ f) g else g f
let app x f = f x
let check x y = if x <= y then () else loop ()
let main () = 
  let i = read_int () in
  app3 (check i) (app i)