(* 停止すればtrueを返す。random.boolが常にtrueを返すときに停止しないので、terminationはinvalid *)
let succ f x k = f (x + 1) k
let rec app f x k = if Random.bool () then app (succ f) (x - 1) k else f x k
let check x y k = if x = y then k true else k false
let main (u:unit) k = app (check 0) 0 k

let () = main () (fun r -> print_string @@ string_of_bool r)

