let s' (k : int -> unit) =
  let rec sum n (k : int -> unit) =
    if n<=0
      then k 0
      else (sum (n - 1) (fun m -> k (m + n)))
  in sum (read_int ()) k

let () =
  s' (fun r -> print_int r)
  