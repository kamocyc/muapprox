(* let rec main x y =
  print_endline "main";
  if read_int () > 0 then
    main x y
  else
    assert (x = y)
  
let rec exists x y =
  print_endline "exists";
  if read_int () > 0 then
    try
      main x y
    with Assert_failure _ -> (try
      main x (-y)
    with Assert_failure _ -> (
      exists x (y - 1)
    )
    )
  else assert (y >= 0)
  
let () =
  let x = read_int () in
  let y = read_int () in
  if y >= 1 + 1 * x && y >= 1 + (-1) * x && y >= 1 then exists x y else ()
 *)

(* exception AA

let main x y =
  if x = y then () else raise AA
  
let rec exists x y =
  assert (y >= 0);
  try
    main x y
  with AA -> (try
    main x (-y)
  with AA -> (
    exists x (y - 1)
  )
  )

let main x y =
  if y >= 1 + 1 * x && y >= 1 + (-1) * x && y >= 1 then exists x y else () *)


exception AA

let main fx y =
  fx (fun x ->
    if x = y then () else raise AA
  )
  
let rec exists fx y =
  assert (y >= 0);
  try
    main fx y
  with AA -> (try
    main fx (-y)
  with AA -> (
    exists fx (y - 1)
  )
  )

let main x y =
  if y >= 1 + 1 * x && y >= 1 + (-1) * x && y >= 1 then exists (fun k -> k x) y else ()

let () = main (read_int ()) (read_int ())