(* ack_loop.in のやつ *)
let lt (a1, b1) (a2, b2) = a1 < a2 || (a1 = a2 && b1 < b2)
let swap (a1, a2) = (a2, a1)

let show (a, b) = "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")"
let show_3 (a, b, c) = "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ", " ^ string_of_int c ^ ")"

let max = List.fold_left (fun acc e -> if acc < e then e else acc) 0

let prev (r1, r2) (m, n, r) =
  let res =
    if r1 - 1 > 0 then (r1 - 1, r2)
    else (1 + max [m], r2 - 1) in
  if fst res > 0 && snd res > 0 && lt (swap res) (swap (r1, r2)) then () else failwith ("res=" ^ show res ^ ", a=" ^ show (r1 ,r2));
  res
  
let rec ack r m n k =
  (* print_endline @@ show (m, n); *)
  (* if not (lt (m, n) r) then failwith "a"; *)
  if m = 0 then k (n + 1)
  else if n = 0 then ack (prev r (m, n, 0)) (m-1) 1 k
  else ack (prev r (m, n, 0)) m (n-1) (fun r' -> ack (prev r (m, n, r')) (m-1) r' k)

let () =
  let m = read_int () in
  let n = read_int () in
  if n>0 && m>0 then
    ack (m+1, n+1) m n (fun r -> print_int r)
  else
    print_int 0