let event s = print_string s

let check x_ k =
  x_ (fun x ->
    if x < 0 then k 1 else k 0
  )

let app (f:((int -> 'a) -> 'a) ->
(((int -> 'a) -> 'a) -> (((int -> 'a) -> 'a) -> 'a) -> 'a) ->
(((int -> 'a) -> 'a) -> 'a) -> 'a) (x_:(int -> 'a) -> 'a) (i:int) kk =
  event "p";
  f x_ (fun x2_ k2 -> x2_ (fun x2 -> k2 ((fun k3 -> k3 (x2 - i))))) kk

let rec ha1 x =
  event "p";
  event "ha";
  ha1 x

let rec ha2 x =
  event "p";
  event "ha";
  ha2 x

let rec walk (x_:(int -> 'a) -> 'a) (f:((int -> 'a) -> 'a) -> (((int -> 'a) -> 'a) -> 'a) -> 'a) k =
  event "p";
  check x_ (fun b ->
    if b = 1 then k x_
    else f x_ (fun x2 -> walk x2 f k)
  )

let rec run x_ f k =
  event "p";
  check x_ (fun b ->
    if b = 1 then k x_
    else f x_ (fun x2 -> f x2 (fun x3 -> run x3 f k))
  )

let rec life x_ =
  if read_int () > 0 then (
    event "p";
    check x_ (fun b ->
      if b = 1 then app walk x_ 1 (fun x__ -> ha1 x__)
      else app run x_ 1 (fun x__ -> ha2 x__)
    )
  ) else life x_

let rec xx flag x_ =
  if flag = 1 then
    life x_
  else
    xx 1 x_
  
let () =
  let x = read_int () in
  xx 0 (fun k -> k x)
