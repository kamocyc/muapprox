let pred2 (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 2)

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let add (f1:unit->int) (f2:unit->int):unit->int =
  let x1 = f1 () in
  let x2 = f2 () in
  (fun u -> x1 + x2)

let check1 f =
  let x = f () in
  if x <  2 then 1
  else 0

let rec fib fn =
  let b = check1 fn in
  if b =  1 then (fun u -> 1)
  else (
    let fr = fib (pred fn) in
    let frr = fib (pred2 fn) in
    add fr frr
  )

let rec x (flag:int) fn =
  if flag = 1 then
    fib fn
  else
    x 1 fn

let m n = x 0 (fun u -> n)

let main () =
  m (Random.int 0) ()
