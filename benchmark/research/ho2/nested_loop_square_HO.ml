let rec main k g =
  check g (fun b ->
    (b != 0 || k 0) &&
    (b  = 0 || main k (pred g))
  )
and mult acc f g k =
  check f (fun b ->
    (b != 0 || k acc) &&
    (b != 1 || mult (add acc g) (pred f) g k)
  )
and add f g k = f (fun fx -> g (fun gx -> k (fx + gx)))
and pred f k = f (fun r -> k (r - 1))
and check f k = f (fun n -> (n > 0 || k 0) && (n <= 0 || k 1))

let main () =
  let n = read_int () in
  mult (fun k -> k 0) (fun k -> k n) (fun k -> k n) (main (fun r -> r = n || true))

let () =
  ignore @@ main ()
