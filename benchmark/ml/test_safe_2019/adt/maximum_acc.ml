
let max x y = if x >= y then x else y
let rec maximum_acc x = function
  | [] -> x
  | y::l -> maximum_acc (max x y) l
let rec maximum = function
  | [] -> assert false
  | x::l -> maximum_acc x l

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main l = if length l > 0 then let _ = maximum l in ()


