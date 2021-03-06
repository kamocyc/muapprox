let rec reverse acc xs =
  match xs with
      [] -> acc
    | x::xs' -> reverse (x::acc) xs'
let reverse xs = reverse [] xs

let rec make_list n =
  if n = 0
  then []
  else n :: make_list (n-1)

let hd xs =
  match xs with
      [] -> assert false
    | x::xs' -> x

let main len =
  let xs = make_list len in
    if len > 0
    then hd (reverse xs)
    else 0
