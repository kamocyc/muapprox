let check (x_:unit->int):int =
  let x = x_ () in
  if x < 0 then 1 else 0

let app f (x_:unit->int) (i:int) (u:unit):int =
  event "P";
  f x_ (fun (x2_:unit -> int) (u:unit) ->
    let x2 = x2_ () in
    x2 - i
  ) u

let rec ha1 (x:unit->int):unit =
  event "P";
  event "Ha";
  ha1 x

let rec ha2 (x:unit->int):unit =
  event "P";
  event "Ha";
  ha2 x

let rec walk (x_:unit -> int) (f:(unit -> int) -> unit -> int) (u:unit): int =
  event "P";
  let b = check x_ in
  if b = 1 then x_ u
  else (
    let x2 = f x_ in
    walk x2 f u
  )

let rec run (x_:unit -> int) (f:(unit -> int) -> unit -> int)(u:unit):int =
  event "P";
  let b = check x_ in
  if b = 1 then x_ u
  else (
    let x2 = f x_ in
    let x3 = f x2 in
    run x3 f u
  )

let rec life (x_:unit->int): unit =
  if Random.int 0 > 0 then (
    event "P";
    let b = check x_ in
    if b = 1 then ha1 (app walk x_ 1)
    else ha2 (app run x_ 1)
  ) else life x_

let rec xx (flag:int) (x_:unit->int):unit =
  if flag = 1 then
    life x_
  else
    xx 1 x_
  
let main =
  let x = Random.int 0 in
  xx 0 (fun (u:unit) -> x)

(*{SPEC}
   fairness: (Always, P)  (* either P does not happen, or *)
   fairness: (Ha, Never) (* Ha happens eventually *)
{SPEC}*)
