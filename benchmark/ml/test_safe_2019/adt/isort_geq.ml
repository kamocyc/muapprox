let rec insert (x:int) ys =
  match ys with
    | [] -> [x]
    | y::ys' ->
        if x < y then x::y::ys'
        else y::(insert x ys')

let rec insertsort xs =
  match xs with
    | [] -> []
    | x::xs' ->
        insert x (insertsort xs')

let rec make_list n =
  if n = 0
  then []
  else Random.int 0 :: make_list (n-1)

let rec length xs =
  match xs with
      [] -> 0
    | _::xs' -> 1 + length xs'

let main n =
  let xs = make_list n in
    assert (length (insertsort xs) >= length xs)
