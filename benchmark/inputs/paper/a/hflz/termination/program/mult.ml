let rec mult m n =
  if m>0 then
    n + mult (m-1) n
  else
    0

let main () =
  let n = read_int () in
  let m = read_int () in
  if m>0 then mult m n else 0
