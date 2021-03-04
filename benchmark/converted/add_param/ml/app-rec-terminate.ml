(* non-terminate *)
let rec loop_ () = loop_ ()
let myassert b = if b then () else loop_ ()

let apply f x = f x
let check x y = myassert (x = y)
let rec loop n nn : unit =
  apply (check n) n;
  if nn > 0 then
    loop (n + 1) (nn - 1)
  
let main () =
  let x = read_int () in
  let y = read_int () in
  loop x y