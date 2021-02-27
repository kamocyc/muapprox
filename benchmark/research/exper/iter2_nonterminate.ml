let rec loop i k =
  if i = 0 then k 0
  else loop (i - 1) k

(* mに依存するあるnで停止しない *)
(* n > m のとき、停止しない *)
let () =
  let m = read_int () in
  let n = read_int () in
  loop (m - n) (fun r -> print_int r)
