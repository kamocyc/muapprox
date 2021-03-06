
let rec combine xs ys = match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (x, y) :: combine xs ys
  | _ -> assert false


let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main (xs: int list) (ys: int list) =
  if length xs = length ys then
    combine xs ys
  else
    []

