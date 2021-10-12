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

let rec mult fm fn =
  let bm = check1 fm in
  if bm =  1 then
    let fr = mult (pred fm) fn in
    add fr fn
  else (fun u -> 0)

let rec x flag fm fn =
  if flag = 1 then
    mult fm fn
  else
    x 1 fm fn

let mult_in m n =
  if m >  0 then x 0 (fun u -> m) (fun k -> n)
  else (fun u -> 0)

let main () =
  mult_in (Random.int 0) (Random.int 0) ()
