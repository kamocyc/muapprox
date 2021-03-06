let lt (a1, b1) (a2, b2) = a1 < a2 || (a1 = a2 && b1 < b2)

let show (a, b) = "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")"
let show_3 (a, b, c) = "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ", " ^ string_of_int c ^ ")"

let rec ack prev m n k =
  (* print_endline @@ show (m, n); *)
  if not (lt (m, n) prev) then failwith "a";
  if m = 0 then k (n + 1)
  else if n = 0 then ack (m, n) (m-1) 1 k
  else ack (m, n) m (n-1) (fun r -> print_endline (show_3 (m, n, r)); ack (m, n) (m-1) r k)

let () =
  let m = read_int () in
  let n = read_int () in
  if n>0 && m>0 then
    ack (m+1, n) m n (fun r -> print_int r)
  else
    print_int 0

(* 
let rec ack m n k =
  if m = 0 then k (n + 1)
  else if n = 0 then ack (m-1) 1 k
  else ack m (n-1) (fun r -> ack (m-1) r k)

let () =
  let m = read_int () in
  let n = read_int () in
  if n>0 && m>0 then
    ack m n (fun r -> print_int r)
  else
    print_int 0 *)
