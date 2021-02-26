let rec loop h n =
  if n > 0 then
    let d = read_int () in
    let n_next = n + d in
    h n_next (loop h)
  else ()
let app n k = k n
let main () = let r = read_int () in loop app r
