
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
let g (r:(unit->int)->unit->int) a =
  r (r a)
in
let rec f fn fm =
  let bn = check1 fn in
  if bn = 1 then succ fm
  else g (f (pred fn)) fm
in
let rec xx (flag:int) fn fm =
  if flag = 1 then
    f fn fm
  else
    xx 1 fn fm
in
let mm n x =
  if (n >= 0 && x >= 0) then xx 0 (fun u -> n) (fun u -> x) ()
  else (fun u -> 0) ()
in
mm (Random.int 0) (Random.int 0)