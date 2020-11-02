
let rec insert x l = match l with
  | []  -> [x]
  | y::l' when x <= y -> x :: l
  | y::l' -> y :: insert x l'
let rec insert_sort l = match l with
  | [] -> []
  | x::l' -> insert x (insert_sort l)

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main l = assert (length l = length (insert_sort l))

