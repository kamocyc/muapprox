
let check i_ n_ =
  let i = i_ () in
  let n = n_ () in
  if i<=n then 1 else 0

let succ n_ (u:unit) =
  let n = n_ () in
  (n + 1)

let rec loop flag i_ n_ y:unit =
  (if flag = 1 then event "Close1" else ());
  let b = check i_ n_ in
  if b = 1 then loop flag (succ i_) n_ y else y ()

let g flag y n_ =
  loop flag (fun u -> 1) n_ y

let rec f x y n_ =
  if Random.int 0 > 0 then
     f x y (succ n_)
  else
    let flag = x () in
    g flag y n_

let rec t (u:unit): unit =
  event "Close2";
  t ()

let s (u:unit) =
  event "Close1";
  1

let rec xx flag s2 t2 n_ =
  if flag = 1 then
    f s2 t2 n_
  else
    xx 1 s2 t2 n_

let main =
  xx 0 s t (fun u -> 0)

(*{SPEC}
   fairness: (Call, Close1)  (* either Close1 happens only finitely often, or *)
   fairness: (Close2, Never) (* Close2 happens infinitely often *)
{SPEC}*)
