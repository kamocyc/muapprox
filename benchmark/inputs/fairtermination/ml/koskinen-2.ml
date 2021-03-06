let rec print (x:int) :unit = print_string "Print";print x
and rumble x y k =
(*  event "Rumble"; *) 
  if x<y then
    if Random.int(0)>0 then
      rumble (x+1) y k
    else rumble x (y-1) k
  else k x

let main() =
  let a = Random.int(0) in
  let b = Random.int(0) in
  rumble a b (fun r -> rumble a r (fun r' -> print r'))