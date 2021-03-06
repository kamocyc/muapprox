let rec bin n k c =
  if n = 0 then c 1
  else if k <= 0 || k >= n then c 1
  else bin (n - 1) (k - 1) (fun r -> bin (n - 1) k (fun rr -> c (r + rr)))

let () =
  let n = read_int () in
  let k = read_int () in
  if n >= 0 && k >= 0 then bin n k (fun r -> print_int r) else print_int 0


(* 
(* 二項係数 *)
let rec bin n k =
  if n = 0 then 1
  else if k <= 0 || k >= n then 1
  else bin (n - 1) (k - 1) + bin (n - 1) k

let () =
  let n = read_int () in
  let k = read_int () in
  print_int @@
    if n >= 0 && k >= 0 then bin n k else 0 *)

