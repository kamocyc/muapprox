let rec map f xs =
  match xs with
  | [] -> []
  | x::xs' -> f x :: map f xs'

let rec rand_pos () =
  let n = Random.int 0 in
  if n > 0 then
    n
  else
    rand_pos ()

let rec make_pos_list n =
  if n <= 0 then
    []
  else
    rand_pos() :: make_pos_list (n-1)

let rec for_all f xs =
  match xs with
  | [] -> true
  | x::xs' -> f x && for_all f xs'

let neg x = -x

let main n =
  let xs = make_pos_list n in
  let ys = map neg xs in
  let zs = map neg ys in
  assert (for_all (fun z -> z > 0) zs)
