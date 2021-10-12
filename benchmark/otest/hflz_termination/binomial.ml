let check1 f =
  let x = f () in
  if x =  0 then 1 else 0

let check2 fk fn =
  let k = fk () in
  let n = fn () in
  if k <= 0 || k >= n then 1
  else 0

let pred (fx:unit->int):unit->int =
  let x = fx () in
  (fun u -> x - 1)


let add (f1:unit->int) (f2:unit->int):unit->int =
  let x1 = f1 () in
  let x2 = f2 () in
  (fun u -> x1 + x2)

let rec bin fn fk =
  let bn = check1 fn in
  let bk = check2 fk fn in
  if bn = 1 then (fun u -> 1)
  else (
    if bk = 1 then
      (fun u -> 1)
    else
      let fr = bin (pred fn) (pred fk) in
      let frr = bin (pred fn) fk in
      (add fr frr)
  )

let rec x flag fn fk =
  if flag = 1 then
    bin fn fk
  else x 1 fn fk

let m n k =
  if (n >= 0 && k >= 0)
  then x 0 (fun u -> n) (fun u -> k)
  else fun u -> 0

let main () =
  m (Random.int 0) (Random.int 0) ()
