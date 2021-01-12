let rec foldr (h : int -> int -> (int -> 'a) -> 'a) (e : int) (l : int) k =
  if l = 0 then k e
           else foldr h e (l-1) (fun r -> h (read_int()) r k)
let sum m n k = k (m + n)
let main (u:unit) k =
  let l = read_int() in
  if l >= 0 then
    foldr sum (read_int()) l k
  else k 0
let () = main () (fun r -> print_int r)

(* let rec foldr (h : int -> int -> int) (e : int) (l : int) =
  if l = 0 then e
           else h (read_int ()) (foldr h e (l-1))
let sum m n = m + n
let main (u:unit) =
  let l = read_int () in
  if l >= 0 then
    foldr sum (read_int ()) l
  else 0

let () = main () |> print_int *)