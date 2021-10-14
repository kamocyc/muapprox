
let check1 f =
  let x = f () in
  if x > 0 then 1
  else 0

in
let check2 f =
  let x = f () in
  if x >= 0 then 1
  else 0

in
let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

in
let g (u:unit) = ()

in
let rec f fx u =
  let b = check1 fx in
  if b =  1 then
    let m = Random.int 0 in
    app (fun u -> m) f (pred fx) u
  else g u
and app fi h fv u =
  let b = check2 fi in
  if b =  1 then app (pred fi) h fv u
  else h fv u

in
let rec xx (flag:int) fn u =
  if flag = 1 then
    f fn u
  else
    xx 1 fn u

in
let mm n =
  xx 0 (fun u -> n) ()
in
mm (Random.int 0)
