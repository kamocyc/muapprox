
let succ i_ (u:unit) =
  let i = i_ () in
  i + 1

let check i_ s_ =
  let i = i_ () in
  let s = s_ () in
  if i<1024 && s<>0 then 1 else 0

let rec inner_loop i_ s_ =
  let b = check i_ s_ in
  if b = 1 then (
    let s = Random.int 0 in
    inner_loop (succ i_) (fun u -> s)
  ) else (
    event "C"
  )

let rec xx flag i_ s_ =
  if flag = 1 then
    inner_loop i_ s_
  else
    xx 1 i_ s_

let rec loop () =
  xx 0 (fun u -> 0) (fun u -> 0);
  event "B";
  loop ()
let main =
  loop ()

(*{SPEC}
   fairness: (B, Never)
   fairness: (Always, C)
{SPEC}*)
