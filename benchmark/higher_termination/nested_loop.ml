let rec loop1 n1 k = if n1 > 0 then loop1 (n1-1) k else k 0
let rec loop2 n2 k = if n2 > 0 then loop1 n2 (fun r1 -> loop2 (n2-1) (fun r2 -> k (r1 + r2))) else k 0

let () =
  let i = read_int () in
  loop2 i (fun r -> print_int r)


(* let rec loop1 n1 = if n1>0 then loop1 (n1-1) else 0
let rec loop2 n2 = if n2>0 then loop1 n2 + loop2 (n2-1) else 0

let () =
  let i = read_int () in
  print_int (loop2 i) *)
