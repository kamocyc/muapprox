
let const (x:unit -> int) () = x

let rec check flag fx =
  if flag = 1 then
    let x = fx () in
    if x > 0 then 1 else 0
  else
    check 1 fx
    
let rec finish (u:unit): unit =
  event "A";
  finish ()

let pred fx (u:unit) =
  let x = fx () in
  (x - 1)

let rec f g =
  let fn = g () in
  let b = check 0 fn in
  if b = 1 then
    f (const (pred fn))
  else finish ()

let rec xx flag g =
  if flag = 1 then
    f g
  else
    xx 1 g

let main =
  let n = Random.int 0 in
  xx 0 (const (fun u -> n))

(*{SPEC}
  fairness: (A, Never)
{SPEC}*)
