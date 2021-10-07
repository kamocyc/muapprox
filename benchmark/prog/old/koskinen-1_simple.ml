let event x = print_string x

let rec finish () = event "done"; finish ()

and explore x r =
  event "explore";
  reduce x r (fun y ->
    if y<=0 then finish ()
    else explore y r
  )

and reduce x r k =
  if x<=0 then k x else r x k

let () =
  let x = read_int () in
  explore x (fun x k -> k (x - 2))
