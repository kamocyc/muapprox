let rec loop1 n1 = if n1>0 then loop1 (n1-1) else 0 in
let rec loop2 n2 = if n2>0 then loop1 n2 + loop2 (n2-1) else 0 in
loop2 (Random.int 0)
