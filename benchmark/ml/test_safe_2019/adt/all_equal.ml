
let rec replicate x n =
  if n <= 0 then
    []
  else
    x :: replicate x (n-1)

let rec all_equal x l = match l with
  | [] -> ()
  | y::ys -> assert(x=y); all_equal y ys

let main x n = all_equal x (replicate x n)

