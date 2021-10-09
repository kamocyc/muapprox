let event s = print_string @@ s ^ ","

let rec loop i y n k =
  if i < n then 
    (event "read_l"; loop (i + 1) y n k) else y k

let g y n k = loop 0 y n k
  
let rec f x y n k =
  if read_int() = 0 then (
    event "read_f";
    f x y (n+1) k
  ) else (
    x (fun () -> g y n k)
  )

let () =
  let s = (fun k -> event "close_in"; k ()) in
  let t = (fun k -> event "close_out"; k ()) in
  f s t 0 (fun () -> ())



(* 
let close1 x = ()
let close2 x = ()

let b = false

let rec g y n =
  for i = 1 to n do
    ()
  done;
  y ()

let rec f x y n =
  if b then (
    f x y (n+1)
  ) else (
    x ();
    g y n
  )

let () =
  let s = (fun () -> close1 ()) in
  let t = (fun () -> close2 ()) in
  f s t 0 *)

(* 
(* original *)
let read x = ()
let write x = ()
let close x = ()

let b = false

let rec g y n =
  for i = 1 to n do
    write y
  done;
  close y

let rec f x y n =
  if b then (
    read x;
    f x y (n+1)
  ) else (
    close x;
    g y n
  )

let () =
  let s = open_in "socket1" in
  let t = open_out "socket2" in
  f s t 0 *)