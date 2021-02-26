let rec ack m n =
  if m = 0 then n + 1
  else if n = 0 then ack (m-1) 1
  else ack (m-1) (ack m (n-1))
let main (u : unit) =
  let m = Random.int 0 in
  let n = Random.int 0 in
  if n>0 && m>0 then
    ack m n
  else
    0
