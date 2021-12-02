
let check1 f =
  let x = f () in
  if x = 0 then 1
  else 0

let succ (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x + 1)

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let rec ack fm fn =
  let b = check1 fm in
  if b = 1 then succ fn
  else (
    let bn = check1 fn in
    if bn = 1 then ack (pred fm) (fun u -> 1)
    else
      let fr = ack fm (pred fn) in
      ack (pred fm) fr
  )
let rec x (flag:int) fm fn =
  if flag = 1 then
    ack fm fn
  else
    x 1 fm fn

let mm m n =
  if m > 0 && n > 0 then
    x 0 (fun u -> m) (fun u -> n)
  else
    (fun u -> 0)

let main () =
  mm (Random.int 0) (Random.int 0) ()
