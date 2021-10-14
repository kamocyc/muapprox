
let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)
in
let gt (lb:int) fn =
  let n = fn () in
  if n > lb then 1 else 0
in
let rec f fx p =
  let b = p fx in
  if b = 1 then f (pred fx) p
  else ()
in
let rec xx (flag:int) fn p =
  if flag = 1 then
    f fn p
  else
    xx 1 fn p
in
let mm n =
  xx 0 (fun u -> n) (gt 0)
in
mm (Random.int 0)
