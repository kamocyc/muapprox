let app h v k = h () v k
let id (u:unit) k = k u
let rec g (x:int) (u:unit) uu k =
  if x = 0 then id uu k else app (g (x-1)) uu k
let main () =
  let r = read_int () in
  g r () () (fun r -> ())
let () = main ()
