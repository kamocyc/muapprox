let rec ack m n k =
  if m = 0 then k (n + 1)
  else if n = 0 then ack (m-1) 1 k
  else ack m (n-1) (fun r -> ack (m-1) r k)

let main k =
  (* let m = Random.int 0 in
  let n = Random.int 0 in *)
  let m = read_int () in
  let n = read_int () in
  if n>0 && m>0 then
    ack m n k
  else
    k 0
  
let () = 
  main (fun r -> print_int r)
  
