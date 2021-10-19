let rec finish ()  :unit  =
  event "Done";
  finish ()

let rec check flag x_ =
  if flag = 1 then
    let x = x_ () in
    if x <= 0 then 1 else 0
  else
    check 1 x_
  
let reduce x_ r =
  let b = check 0 x_ in
  if b = 1 then x_ else r x_

let rec explore x_ r  :unit =
  let y_ = reduce x_ r in
  let b = check 0 y_ in
  if b = 1 then finish ()
  else explore y_ r

let rec xx flag x_ r= 
  if flag = 1 then
    explore x_ r
  else
    xx 1 x_ r

let main =
  let x = Random.int 0 in
  xx 0 (fun u -> x) (fun xx_ (u:unit) ->
    let x = xx_ () in
    x - 2
  )

(*{SPEC}
   fairness: (Done, Never)
{SPEC}*)
