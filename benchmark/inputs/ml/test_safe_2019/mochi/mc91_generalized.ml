
let mc_k k r n =
  let d = r - k + 1 in
  let rec f n =
    if n > r
      then n - d
      else f (f (n + d + 1))
  in f n

let main k r n =
  if n <= r then assert (mc_k k r n = k)

