let app f (x:int) u k = f x u k
let id (u:unit) k = k u
let rec g (x:int) u k =
  if x=0 then id u k else app g (x-1) u k
let main () =
  let t = read_int () in g t () (fun f -> ())

let () = main ()
