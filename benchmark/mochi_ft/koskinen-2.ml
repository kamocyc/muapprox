let rec print (x_:unit->int):unit =
  event "Print";
  print x_

let succ x_ (u:unit)=
  let x = x_ () in
  (x + 1)

let pred x_ (u:unit)=
  let x = x_ () in
  (x - 1)

let check (x_:unit->int) (y_:unit->int) =
  let x = x_ () in
  let y = y_ () in
  if x < y then 1 else 0
  
let rec rumble x_ y_ =
  let b = check x_ y_ in
  if b = 1 then
    if Random.int 0 > 0 then
      rumble (succ x_) y_
    else rumble x_ (pred y_)
  else x_

let rec xx flag a_ b_: unit =
  if flag = 1 then
    let r_ = rumble a_ b_ in
    let r2_ = rumble a_ r_ in
    print r2_
  else
    xx 1 a_ b_
    
let main =
  let a = Random.int 0 in
  let b = Random.int 0 in
  xx 0 (fun u -> a) (fun u -> b)

(*{SPEC}
   fairness: (Print, Never)
{SPEC}*)