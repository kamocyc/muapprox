let make_array = (fun i -> 0)
let update ar i x =
  fun j -> if j = i then x else ar j
let check ar i x =
  (ar i) = x
let rec loop f i =
  let r = f () in
  if r <= i then 0
  else 1 + loop f (i + 1)

let rec set ar n = 
  if n <= 0 then
    ar
  else
    let ar = update ar n n in
    set ar (n - 1)

let rec sum ar acc n =
  if ar n = 0 then
    acc
  else
    let e = ar n in
    let acc2 = fun () -> acc () + e in
    sum ar acc2 (n - 1)

(* input 10 -> output 55 *)
let main () =
  let n = read_int () in  
  let ar = make_array in
  let ar = set ar n in
  let s = sum ar (fun () -> 0) n in
  loop s 0
