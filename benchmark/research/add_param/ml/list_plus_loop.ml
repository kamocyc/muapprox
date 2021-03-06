let nil = (0, fun i -> 0)
let cons a (len, l) =
  (len + 1, fun i -> if i = 0 then a else l (i - 1))
let hd (len, l) = l 0
let tl (len, l) = (len - 1, fun i -> l (i + 1))
let is_nil (len, l) = len = 0

let rec loop ls =
  let x = hd ls in
  let y = hd (tl ls) in
  if x + y > 0 then
    loop (cons (x - 1) (cons y nil))
  else
    0
  
let main () =
  let x = read_int () in
  let y = read_int () in
  loop (cons x (cons y nil))
  