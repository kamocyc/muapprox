let gt lb (n : int) = n > lb in
let rec f (x : int) p =
  if p x then
    f (x-1) p
  else
    ()
in
f (Random.int 0) (gt 0)
