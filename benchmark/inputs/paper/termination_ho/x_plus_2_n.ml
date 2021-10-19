
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

let g r a =
  r (r a)

let rec f fn fm =
  let bn = check1 fn in
  if bn = 1 then succ fm
  else g (f (pred fn)) fm


let rec xx (flag:int) fn fm =
  if flag = 1 then
    f fn fm
  else
    xx 1 fn fm
  
let main () =
  let n = Random.int 0 in
  let x = Random.int 0 in
  if (n >= 0 && x >= 0) then xx 0 (fun u -> n) (fun u -> x) ()
  else (fun u -> 0) ()
