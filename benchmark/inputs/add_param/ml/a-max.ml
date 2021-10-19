let rec loop () = loop ()
let myassert b = if b then () else loop ()
let rec array_max i n ar m =
  if i >= n then
    m
  else
    let x = ar i in
    let z = if x > m then x else m in
    array_max (i + 1) n ar z
let rec rand_array x i = Random.int (x + 1)
let main () =
  let n = read_int () in
  let x = read_int () in
  if n > 0 && x >= 0 then
    let m = array_max 0 n (rand_array x) (-1) in
    myassert (m <= x)