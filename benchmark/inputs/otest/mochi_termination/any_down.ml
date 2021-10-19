let check (f:unit->int):int=
  let x = f () in
  if x > 0 then 1
  else 0
in
let sub (fn:unit->int) (r:int): unit -> int =
  let n = fn () in
  (fun x -> n - r)
in
let rec f1 (fn_next:unit->int):unit =
  let b = check fn_next in
  if b = 1 then f fn_next
  else ()
and f (fn:unit->int):unit =
  let r = Random.int 0 in
  if r > 0 then
    f1 (sub fn r)
  else
    f1 (sub fn (1 - r))
in
let rec x (flag:int) (fn:unit->int):unit =
  if flag = 1 then
    f fn
  else
    x 1 fn
in
let m n = x 0 (fun u -> n) in
  m (Random.int 0)
