let pred x k = k (x - 1)
let compose (f : int -> (int -> 'a) -> 'a) (g : int -> (int -> 'a) -> 'a) x k = g x (fun r -> f r k)
let id (x : int) k = k x
let succ x k = k (x + 1)
let rec toChurch fn f x k =
  fn (fun n -> if n = 0 then id x k else compose f (toChurch (pred n) f) x k)

let check fn k =
  fn (fun n ->
    if n >= 0 then k 1 (fun k -> k n)
    else k 0 (fun k -> k n)
  )
  
let () =
  (fun ff -> ff (fun k -> let x = read_int () in k x))
  (fun fn ->
    check fn (fun b fnn ->
      if b = 1 then
        let tos = toChurch fnn succ in
        let y = read_int () in
        tos y (fun r -> print_int r)
      else ()
    )
  )
  
(* 
0 0
0 1
0 -1
1 0
1 1
1 -1
-1 -
 *)