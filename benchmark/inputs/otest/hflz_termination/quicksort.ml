

let comp (fx:unit->int) (fy:unit->int):int =
  let x = fx () in
  let y = fy () in
  if x >= y then 1
  else 0

let pred (fx:unit->int):(unit->int) =
  let x = fx () in
  (fun u -> (x - 1))

let succ (fx:unit->int):(unit->int) =
  let x = fx () in
  (fun u -> x + 1)

let check1 (f:unit->int):int =
  let x = f () in
  if x <= 0 then 1
  else 0

let addP1 (f1:unit->int) (f2:unit->int):unit->int =
  let x1 = f1 () in
  let x2 = f2 () in
  (fun u -> x1 + 1 + x2)

let rec qs (cmp:(unit -> int) -> (unit -> int) -> int) fn =
  let b = check1 fn in
  if b = 1 then (fun u -> 0)
  else (
    let m = Random.int 0 in
    x2 0 cmp (fun u -> m) (fun u -> 0) (fun u -> 0) (pred fn) 
  )
and x2 flag (cmp:(unit -> int) -> (unit -> int) -> int) fx fl fr fxs =
  if flag = 1 then
    par cmp fx fl fr fxs
  else x2 1 cmp fx fl fr fxs
and par (cmp:(unit -> int) -> (unit -> int) -> int) fx fl fr fxs =
  let bxs = check1 fxs in
  if bxs = 1 then
    let r' = qs cmp fl in
    let r'' = qs cmp fr in
    addP1 r' r''
  else (
    let m = Random.int 0 in
    let r' = cmp (fun u -> m) fx in
    if r' = 1 then par cmp fx (succ fl) fr (pred fxs)
    else par cmp fx fl (succ fr) (pred fxs)
  )

let rec xx flag (f:(unit -> int) -> (unit -> int) -> int) fn =
  if flag = 1 then
    qs f fn
  else xx 1 f fn

let mm n =
  xx 0 comp (fun u -> n)

let main () =
  mm (Random.int 0) ()
