(* katsura-solverで型が付かない *)
let rec loop () = loop ()
let add x1 x2 = x1 + x2
let rec repeat f k x = if k <= 0 then x else f (repeat f (k - 1) x)
let main () =
  let n = read_int () in
  let k = read_int () in
  if n >= 0 && k > 0 then
    if (repeat (add n) k 0 >= n) then () else loop ()