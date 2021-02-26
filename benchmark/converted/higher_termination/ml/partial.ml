let gt lb (n : int) = n > lb
let rec f (x : int) p =
  if p x then
    f (x-1) p
  else
    ()

let main () =
  f (read_int ()) (gt 0)
