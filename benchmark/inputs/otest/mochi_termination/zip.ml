let check1 f =
  let x = f () in
  if x <= 0 then 1
  else 0
in
let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)
in
let succ (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x + 1)
in
let rec zip fxs fys =
  let bx = check1 fxs in
  let by = check1 fys in
  if bx = 1 then (fun u -> 0)
  else (
    if by = 1 then
      (fun u -> 0)
    else
      let r = zip (pred fxs) (pred fys) in
      succ r
  )
in
let rec xx (flag:int) fxs fys =
  if flag = 1 then
    zip fxs fys
  else
    xx 1 fxs fys
in
let m x y = xx 0 (fun u -> x) (fun u -> y) in
m (Random.int 0) (Random.int 0)

