let rec map2 f xs ys =
  match xs, ys with
  | [],[] -> []
  | x::xs',y::ys' -> f x y :: map2 f xs' ys'

let rec for_all f xs =
  match xs with
  | [] -> true
  | x::xs' -> f x && for_all f xs'

let rec rand_pos () =
  let n = Random.int 0 in
  if n > 0 then
    n
  else
    rand_pos ()

let rec rand_neg () =
  let n = Random.int 0 in
  if n < 0 then
    n
  else
    rand_neg ()

let const0 () = 0

let rec make_list f n =
  if n = 0 then
    []
  else
    f() :: make_list f (n-1)

let add x y = x + y
let sub x y = x - y

let rec for_all f xs =
  match xs with
  | [] -> true
  | x::xs' -> f x && for_all f xs'

let main n =
  let zero = make_list const0 n in
  let pos = make_list rand_pos n in
  let neg = make_list rand_neg n in
  let xs = map2 add zero pos in
  let ys = map2 sub xs neg in
  assert (for_all (fun y -> y > 0) ys)
