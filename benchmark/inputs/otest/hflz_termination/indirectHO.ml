let app h (v:unit) = (h () v: unit)

let id (x:unit) = x

let check1 f =
  let x = f () in
  if x >  0 then 1
  else 0

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let rec f fn u x =
  let b = check1 fn in
  if b  = 1 then app (f (pred fn)) x
  else id x

let rec xx (flag:int) fn u x =
  if flag = 1 then
    f fn u x
  else
    xx 1 fn u x

let m n = xx 0 (fun u -> n) () ()

let main () =
  m (Random.int 0)
