let rec main2 f =
  f (fun m ->
    if m > 0 then
      main2 (fun k -> k (m - 1))
    else
      ()
  )
  
let rec main n f =
  if n > 0 then
    (main2 f;
    main (n - 1) f)
  else
    ()
  
let () =
  let n = read_int () in
  let m = read_int () in
  main n (fun k -> k m)
