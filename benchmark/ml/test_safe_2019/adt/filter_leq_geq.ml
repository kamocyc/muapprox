let rec filter f xs =
  match xs with
  | [] -> []
  | x::xs' ->
      if f x then
        x :: filter f xs'
      else
        filter f xs'

let rec for_all f xs =
  match xs with
  | [] -> true
  | x::xs' -> f x && for_all f xs'

let leq_zero x = x <= 0
let geq_zero x = x >= 0
let eq_zero x = x = 0

let main xs =
  let ys = filter leq_zero xs in
  let zs = filter geq_zero ys in
  assert (for_all eq_zero zs)
