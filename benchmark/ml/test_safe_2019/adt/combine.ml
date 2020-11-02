
let rec combine xs ys = match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (x, y) :: combine xs ys
  | _ -> assert false

let main xs = combine xs xs

