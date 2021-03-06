
let fold_nat f n x0 =
  let rec go i x =
    if i < n
      then go (i + 1) (f i x)
      else x
  in go 0 x0

let sum n = fold_nat (fun i x -> i + x) (n + 1) 0

let main n = if n >= 0 then assert (sum n >= 0)

