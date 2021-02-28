let make_array = (fun i -> 0)
let update ar i x =
  fun j -> if j = i then x else ar j
let check ar i x =
  (ar i) = x
let rec loop f ar n i =
  let r = (f ar n) - i in
  if r <= 0 then 0
  else 1 + loop f ar n (i + 1)

let rec set ar n = 
  if n <= 0 then
    ar
  else
    let ar = update ar n n in
    set ar (n - 1)

let rec sum ar n =
  if ar n = 0 then
    0
  else
    let e = ar n in
    let r = sum ar (n - 1) in
    r + e

(* invalid *)
(* input 10 -> output 55 *)
let main () =
  let n = read_int () in  
  let ar = make_array in
  let ar = set ar n in
  loop sum ar n 0
