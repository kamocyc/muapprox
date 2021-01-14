let lambda x k = k (x + 1)
let rec f x y k = if x > 0 then f (x - 1) y k else lambda y k
let g y k = f 1 y k

let () =
  g 2 (fun r -> print_int r)

(* 
(* 結局 x + 1が計算される *)
let lambda x = x + 1
let rec f x = if x > 0 then f (x - 1) else lambda
let g = f 1

let () =
  g 2 |> print_int *)
