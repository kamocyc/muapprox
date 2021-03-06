let nil = (0, fun i -> 0)
let cons a (len, l) =
  (len + 1, fun i -> if i = 0 then a else l (i - 1))
let hd (len, l) = l 0
let tl (len, l) = (len - 1, fun i -> l (i + 1))
let is_nil (len, l) = len = 0

let rec loop f ls i =
  let r = (f ls) - i in
  if r <= 0 then 0
  else 1 + loop f ls (i + 1)
  
let rec set ls n = 
  if n <= 0 then
    ls
  else
    set (cons n ls) (n - 1)

let rec sum ls =
  if hd ls = 0 then
    0
  else
    let e = hd ls in
    let r = sum (tl ls) in
    r + e
  
let main () =
  let n = read_int () in
  let ls = set nil n in
  loop sum ls 0
  