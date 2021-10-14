
let check1 f =
  let x = f () in
  if x > 100 then 1
  else 0
in
let add_int11 (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x + 11)
in
let sub_int10 (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 10)
in
let rec mc fn =
  let b = check1 fn in
  if b = 1 then sub_int10 fn
  else
    let r = mc (add_int11 fn) in
    mc r
in
let rec x (flag:int) fn =
  if flag = 1 then
    mc fn
  else
    x 1 fn
in
let m n = x 0 (fun u -> n)
in
  m (Random.int 0) ()
