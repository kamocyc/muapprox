
let pred (fx:unit->int):(unit->int) =
  let x = fx () in
  (fun u -> (x - 1))

let check1 (f:unit->int):int =
  let x = f () in
  if x > 0 then 1
  else 0

let rec f fm fn =
  let bm = check1 fm in
  let bn = check1 fn in
  let r = Random.int 0 in
  if r > 0 && bm = 1 then
    f (pred fm) fn
  else (
    if r <= 0 && bn = 1 then
      f fm (pred fn)
    else
      ()
  )

let rec xx (flag:int) fm fn =
  if flag = 1 then
    f fm fn
  else
    xx 1 fm fn

let main () =
  let m = Random.int 0 in
  let n = Random.int 0 in
  xx 0 (fun u -> m) (fun u -> n)
