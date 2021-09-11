let event x = print_string x

let rec print x =
  event "print"; print x

and rumble x y k =
  event "rumble";
  if x < y then (
    if read_int () = 0 then
      rumble (x+1) y k
    else rumble x (y-1) k
  ) else k x

let () =
  let a = read_int () in
  let b = read_int () in
  rumble b a (fun r -> rumble a r (fun r2 -> print r2))
