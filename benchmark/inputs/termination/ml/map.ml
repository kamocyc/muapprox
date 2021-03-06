
(* 乱数列に3を足して、総和を取る *)
let rec map f xs k =
  if xs = 0 then k 0
  else f (read_int ()) (fun r -> map f (xs - 1) (fun r' -> k (r + r')))

let compose (f : int -> (int -> 'a) -> 'a) (g : int -> (int -> 'a) -> 'a) x k = g x (fun r -> f r k)
let add x y k = k (x + y)
let main k =
  let l = read_int () in
  if l >= 0 then map (compose (add 1) (add 2)) l k
            else k 0

let () =
  main (fun r -> print_int r)
(* 
(* 乱数列に3を足して、総和を取る *)
let rec map f xs =
  if xs = 0 then 0
  else f (read_int ()) + map f (xs - 1)
let compose (f : int -> int) (g : int -> int) x = f (g x)
let add x y = x + y
let main () =
  let l = read_int () in
  if l >= 0 then map (compose (add 1) (add 2)) l
            else 0

let () =
  main () |> print_int *)