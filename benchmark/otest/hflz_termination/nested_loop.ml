let check1 f =
  let x = f () in
  if x > 0 then 1
  else 0

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)

let add (f1:unit->int) (f2:unit->int):unit->int =
  let x1 = f1 () in
  let x2 = f2 () in
  (fun u -> x1 + x2)

let rec loop1 (fn1:unit->int):unit->int =
  let b = check1 fn1 in
  if b = 1 then loop1 (pred fn1)
  else (fun u -> 0)

let rec loop2 (fn2:unit->int):unit->int =
  let b = check1 fn2 in
  if b =  1 then
    let r1 = loop1 fn2 in
    let r2 = loop2 (pred fn2) in
    add r1 r2
  else (fun u -> 0)

let rec x flag fn =
  if flag = 1 then
    loop2 fn
  else
    x 1 fn

let m n = x 0 (fun u -> n)

let main () =
  m (Random.int 0) ()
