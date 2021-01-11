let rec f m n k =
  let r = read_int () in
  if r > 0 && m > 0 then f (m-1) n k
  else if r <= 0 && n > 0 then f m (n-1) k
  else k ()
  
let () =
  let n = read_int () in
  let m = read_int () in
  f n m (fun r -> ())


(* fの呼び出しのたびに引数のいずれかが必ず減少するか停止する *)
(* 
let rec f m n =
  let r = read_int () in
  if r > 0 && m > 0 then f (m-1) n
  else if r <= 0 && n > 0 then f m (n-1)
  else ()
  
let () =
  let n = read_int () in
  let m = read_int () in
  f n m *)
