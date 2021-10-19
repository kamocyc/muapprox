
let check x_ =
  let x = x_ () in
  if x < 0 then 1
  else if x = 0 then 2
  else 3

let rec f x_ =
  let b = check x_ in
  if b = 1 then ()
  else if b = 2 then (event "A")
  else (
    f (fun u -> 0);
    f (fun u -> 1)
  )

let rec xx flag x_ =
  if flag = 1 then
    f x_
  else
    xx 1 x_

let main () =
  let x = Random.int 0 in
  xx 0 (fun u ->  x)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*)
