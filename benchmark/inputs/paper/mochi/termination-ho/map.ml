
let check1 f =
  let x = f () in
  if x = 0 then 1
  else 0

in
let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

in
let add x y = x + y

in
let compose (f:int -> int) (g:int -> int) x = f (g x)

in
let rec map f fxs =
  let b = check1 fxs in
  if b =  1 then 0
  else
    let m = Random.int 0 in
    let r = f m in
    let r' = map f (pred fxs) in
    r + r'

in
let rec xx (flag:int) fl =
  if flag = 1 then
    map (compose (add 1) (add 2)) fl
  else
    xx 1 fl

in
let mm l =
  if l >= 0 then xx 0 (fun u -> l)
  else 0
in
mm (Random.int 0)
