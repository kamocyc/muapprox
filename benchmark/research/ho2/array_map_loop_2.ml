(* タイムアウトするので解けない *)
let make_array = (fun (i : int) -> 0)
let update ar (i : int) (x : int) =
  fun j -> if j = i then x else ar j

let check ar (i : int) (j: int) =
  let x = ar i in
  let y = ar j in
  x + y <= 0

let pred ar i =
  let x = ar i in
  update ar i (x - 1)
  
let rec loop ar i j =
  if check ar i j then 0
  else (
    let ar = pred ar 0 in
    loop ar 0 1 
  )

(* 配列の要素を2乗する *)
let rec map ar f n =
  if n >= 0 then
    let ar = update ar n (f (ar n)) in
    map ar f (n - 1)
  else
    ar

(* input 10 -> output 55 *)
let main () =
  let x = read_int () in
  let y = read_int () in
  let ar = make_array in
  let ar = update ar 0 x in
  let ar = update ar 1 y in
  let ar = map ar (fun i -> i * i) 1 in
  loop ar 0 1
