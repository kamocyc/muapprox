
let rec halt (u:unit):unit =
  halt ()

let check1 (x_:unit->int):int =
  let x = x_ () in
  if x>0 then 1 else 0

let pred (x_:unit->int) (u:unit):int =
  let x = x_ () in
  x - 1
  
let rec bar (x_:unit->int):unit->int =
  let b = check1 x_ in
  if b = 1 then bar (pred x_) else x_

let check2 (x_:unit->int):int =
  let x = x_ () in
  if x<=0 then 1 else 0

let rec foo (x_:unit->int):unit =
  event "Foo";
  let b = check2 x_ in
  if b = 1 then foo x_ else halt ()

let rec xx flag x_ =
  if flag = 1 then (
    if Random.int 0 > 0 then foo (fun u -> 0)
    else (
      let r_ = bar x_ in
      foo r_
    )
  ) else
    xx 1 x_

let main =
  let x = Random.int 0 in
  xx 0 (fun u -> x)

(*{SPEC}
   fairness: (Foo, Never)
{SPEC}*)
