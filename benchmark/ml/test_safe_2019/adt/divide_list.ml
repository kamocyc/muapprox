
let rec length (l: int list) = match l with
  | [] -> 0
  | _::l -> 1 + length l

let rec divide (l : int list) = match l with
  | [] -> [], []
  | [x] -> [x], []
  | x::y::l -> let l1, l2 = divide l in x::l1, y::l2

let main l =
  let l1, l2 = divide l in
  assert(length l >= length l1);
  assert(length l >= length l2)

