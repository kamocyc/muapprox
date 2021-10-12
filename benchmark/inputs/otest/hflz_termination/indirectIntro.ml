let check1 f =
  let x = f () in
  if x > 0 then 1
  else 0

let check2 f =
  let x = f () in
  if x >= 0 then 1
  else 0

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let g (u:unit) = ()

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

let rec xx (flag:int) fn u =
  if flag = 1 then
    f fn u
  else
    xx 1 fn u

let main () =
  let n = Random.int 0 in
  xx 0 (fun u -> n) ()
