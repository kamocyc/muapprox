let succ (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x + 1)

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let check1 f =
  let x = f () in
  if x = 0 then 1
  else 0

let id (x:(unit->int)) = x

let compose f g x = f (g x)

let rec toChurch fn f fx =
  let bn = check1 fn in
  if bn =  1
  then id fx
  else compose f (toChurch (pred fn) f) fx
  
let rec xx (flag:int) fn f fx =
  if flag = 1 then
    toChurch fn f fx
  else
    xx 1 fn f fx

let main () =
  let x = Random.int 0 in
  if x >= 0 then
    let y = Random.int 0 in
    xx 0 (fun u -> x) succ (fun u -> y) ()
  else
    0
