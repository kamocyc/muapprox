let rec halt (): unit =
  (* event "Halt"; *)
  halt()
  
let rec bar x k =
(*  event "Bar" *)
  if x>0 then bar (x-1) k
  else k x

let rec foo x =
  print_string "Foo";
  if x<=0 then foo x
  else halt()

let main () =
  let t = Random.int(0) in
     if Random.int(0)>0 then foo 0
     else bar t (fun r -> foo r)
