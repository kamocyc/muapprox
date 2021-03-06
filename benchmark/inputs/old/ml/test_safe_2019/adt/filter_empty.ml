let rec filter f xs =
  match xs with
  | [] -> []
  | x::xs' ->
      if f x then
        x :: filter f xs'
      else
        filter f xs'

let eq_zero x = x = 0
let neg f x = not (f x)

let main xs =
  let ys = filter eq_zero xs in
  let zs = filter (neg eq_zero) ys in
  assert (zs = [])
