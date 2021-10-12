let pred (fx:unit->int):(unit->int) =
  let x = fx () in
  (fun u -> (x - 1))

let succ (fx:unit->int):(unit->int) =
  let x = fx () in
  (fun u -> x + 1)

let check (f:unit->int):int =
  let x = f () in
  if x <= 0 then 1
  else 0

let rec append (fxs:unit->int) (fys:unit->int):(unit -> int) =
  let b = check fxs in
  if b  = 1 then fys
  else
    succ (append (pred fxs) fys)

let rec x (flag:int) (fxs:unit->int) (fys:unit->int):(unit -> int) =
  if flag = 1 then
    append fxs fys
  else
    x 1 fxs fys

let m l1 l2 = x 0 (fun u -> l1) (fun u -> l2)

let main () =
  m (Random.int 0) (Random.int 0) ()
