let rec f n =
  let r = Random.int 0 in
  let delta = if r>0 then r else 1-r in
  let n_next = n - delta in
  if n_next > 0 then
    f n_next
  else
    ()
in
f (Random.int 0)
