
type int_list = int * (int -> int)

let length xs = match xs with (x,_) -> x

let nil = (0, fun x -> assert false)

let is_nil xs = length xs <= 0

let cons x xs = match xs with (l,f) ->
  let l' = l + 1 in
  let f' i = if i = 0 then x else f (i + 1) in
  (l', f')

let un_cons xs = match xs with (l,f) ->
  let x = f 0 in
  let l' = l - 1 in
  let f' i = f (i - 1) in
  (x, (l',f'))

let rec zipwith f xs ys =
  if is_nil xs && is_nil ys
    then nil
    else
      let x, xs' = un_cons xs in
      let y, ys' = un_cons ys in
      cons (f x y) (zipwith f xs' ys')

let rec make_list n =
  if n > 0 then
    cons (Random.int 100) (make_list (n-1))
  else
    nil

let main n =
  let xs = make_list n in
  let ys = make_list n in
  zipwith (fun x y -> x + y) xs ys

