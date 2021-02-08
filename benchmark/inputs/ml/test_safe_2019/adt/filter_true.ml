
let rec filter f xs =
  match xs with
  | [] -> []
  | x::xs' ->
      if f x
      then x :: filter f xs'
      else filter f xs'

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main xs =
  let n = length xs in
  let p (x: int) = true in
  assert (length (filter p xs) <= n)

