
let rec cat_maybes xs = match xs with
  | [] -> []
  | Some(x)::xs -> x :: cat_maybes xs
  | None::xs -> cat_maybes xs

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main xs =
  assert (length xs >= length (cat_maybes xs))

