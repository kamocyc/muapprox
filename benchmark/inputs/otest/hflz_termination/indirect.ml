let app h (v:(unit->int)) (u:unit) = (h v u:unit)

let id (x:unit) = x

let check1 f =
  let x = f () in
  if x >  0 then 1
  else 0

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let rec f fx =
  let b = check1 fx in
  if b =  1 then app f (pred fx)
  else id

let rec x (flag:int) fy y =
  if flag = 1 then
    f fy y
  else
    x 1 fy y

let m n = x 0 (fun u -> n) ()

let main () =
  m (Random.int 0)
