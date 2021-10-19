let rec mult m n =
  if m>0 then
    n + mult (m-1) n
  else
    0
in
let m = Random.int 0 in
let n = Random.int 0 in
if m>0 then mult m n else 0
