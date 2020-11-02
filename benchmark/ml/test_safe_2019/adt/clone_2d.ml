
let rec clone_2d x n =
  let rec clone x m =
    if m > 0 then x :: clone x (m-1) else []
  in
    clone (clone x n) n

let head = function
  | [] -> assert false
  | x::_ -> x

let rec map f = function
  | [] -> []
  | x::l -> f x :: map f l

let main x n = map head (clone_2d x n)

