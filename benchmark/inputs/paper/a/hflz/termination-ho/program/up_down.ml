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

let app (f:(unit -> int) -> unit) x =
  f x

let rec down fx =
  let b = check1 fx in
  if b =  1 then ()
  else down (pred fx)

let rec up fx =
  let b = check1 fx in
  if b =  1 then ()
  else up (succ fx)

let rec x_App_Down flag x =
  if flag = 1 then
    app down x
  else
    x_App_Down 1 x

let rec x_App_Up flag x =
  if flag = 1 then
    app up x
  else
    x_App_Up 1 x

let main () =
  let t1 = Random.int 0 in
  let t2 = Random.int 0 in
  if t1 > 0 then
    x_App_Down 0 (fun u -> t1)
  else (
    if t2 < 0 then
      x_App_Up 0 (fun u -> t2)
    else ()
  )
