let gt lb (n : int) k = if n > lb then k 1 else k 0
let rec f (x : int) p k =
  p x (fun b -> 
    if b = 1 then
      f (x-1) p k
    else
      k ())

let () =
  let i = read_int () in
  f i (gt 0) (fun r -> print_endline "END")

let () =
  let gt lb (n : int) = n > lb in
  let rec f (x : int) p =
    if p x then
      f (x-1) p
    else
      ()
  in
  f (read_int ()) (gt 0)