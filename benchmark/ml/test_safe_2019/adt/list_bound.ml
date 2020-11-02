
let rec assert_bounded x = function
  | [] -> ()
  | y::l -> assert(x >= y); assert_bounded x l

let rec replicate x n =
  if n <= 0 then
    []
  else
    x :: replicate x (n-1)

let main x n = assert_bounded x (replicate x n)

