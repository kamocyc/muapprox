let rec make_list m =
  if m <= 0
  then []
  else Random.int 0 :: make_list (m-1)

let rec make_list_list m =
  if m <= 0
  then []
  else make_list (Random.int 0) :: make_list_list (m-1)

let head = function
    [] -> assert false
  | x::xs -> x

let ne = function
    [] -> 1
  | x::xs -> 0

let rec filter p = function
    [] -> []
  | x::xs -> if p x = 1 then x::(filter p xs) else filter p xs

let rec map f = function
    [] -> []
  | x::xs -> f x :: map f xs

let main m = map head (filter ne (make_list_list m))
