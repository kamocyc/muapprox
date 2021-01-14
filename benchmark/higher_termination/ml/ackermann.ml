let rec ack m n k =
  if m = 0 then k (n + 1)
  else if n = 0 then ack (m-1) 1 k
  else ack m (n-1) (fun r -> ack (m-1) r k)

let () =
  let m = read_int () in
  let n = read_int () in
  if n>0 && m>0 then
    ack m n (fun r -> print_int r)
  else
    print_int 0
