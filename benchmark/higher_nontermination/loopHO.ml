let rec loop h n k =
  if n > 0 then
    let d = read_int () in
    let n_next = n + d in
    h n_next (fun n -> loop h n k)
  else k ()
  
let app n k = k n

let () =
  let r = read_int () in
  loop app r (fun r' -> ())


(* 
let rec loop h n =
  if n > 0 then
    let d = read_int () in
    let n_next = n + d in
    h n_next (loop h)
  else ()
  
let app n k = k n

let main () = let r = read_int () in loop app r *)

