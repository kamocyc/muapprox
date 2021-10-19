
let succ (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x + 1)
in
let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)
in
let check1 f =
  let x = f () in
  if x = 0 then 1
  else 0
in
let app (f:(unit -> int) -> unit) x =
  f x
in
let rec down fx =
  let b = check1 fx in
  if b =  1 then ()
  else down (pred fx)
in
let rec up fx =
  let b = check1 fx in
  if b =  1 then ()
  else up (succ fx)
in
let rec x_App_Down flag x =
  if flag = 1 then
    app down x
  else
    x_App_Down 1 x
in
let rec x_App_Up flag x =
  if flag = 1 then
    app up x
  else
    x_App_Up 1 x
in
let mm t1 t2 =
  if t1 > 0 then
    x_App_Down 0 (fun u -> t1)
  else (
    if t2 < 0 then
      x_App_Up 0 (fun u -> t2)
    else ()
  )
in
mm (Random.int 0) (Random.int 0)
