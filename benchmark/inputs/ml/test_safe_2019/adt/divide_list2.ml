
let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let rec divide x l = match l with
  | [] -> [], []
  | y::l' ->
      let l1, l2 = divide x l' in
      if x <= y
        then y::l1, l2
        else l1, y::l2

let main n l =
  let l1, l2 = divide n l in
  assert(length l >= length l1);
  assert(length l >= length l2)

