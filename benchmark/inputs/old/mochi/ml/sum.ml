let rec sum n =
  if n <= 0 then
    0
  else
    n + sum (n-1)
let main () =
  let n = read_int () in
  sum n

let main () =
  assert (main () = 0)
