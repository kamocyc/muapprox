let rec bin n k =
  if n = 0 then 1
  else if k <= 0 || k >= n then 1
  else bin (n - 1) (k - 1) + bin (n - 1) k
let main (u:unit) =
  let n = Random.int 0 in
  let k = Random.int 0 in
  if n >= 0 && k >= 0 then bin n k else 0
