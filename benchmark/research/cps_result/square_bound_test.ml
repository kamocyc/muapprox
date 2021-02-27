let () =
  let rec mult (n : int) (m : int) (k : int -> unit): unit =
    if m <= 0 then k 0
    else mult n (m - 1) (fun r -> k (n + r)) in
    
  let pred (r : int) (k: int -> unit): unit = k (r - 1) in

  let rec loop (f : (int -> unit) -> unit): unit =
    f (fun r ->
      if r <= 0 then ()
      else loop (pred r)) in

  let n = Random.int 0 in
  loop (mult n n)
