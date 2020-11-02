
let rec assert_bounded x = function
  | [] -> ()
  | y::l -> assert(x >= y); assert_bounded x l

let rec make_list n =
  if n <= 0 then
    []
  else
    n :: make_list (n-1)

let main x n = assert_bounded n (make_list n)

