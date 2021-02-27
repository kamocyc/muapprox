let rec gcd a b k =
  if a > b then gcd (a - b) b k
  else if a < b then gcd a (b - a) k
  else k a

let () =
  let n = read_int () in
  let m = read_int () in
  (* should be n >= 1 /\ m >= 1 *)
  gcd n m (fun r -> print_int r)
