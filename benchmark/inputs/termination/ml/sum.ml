let rec sum n = if n<=0 then 0 else n + sum (n-1) in sum (Random.int 0)

(* 
let rec sum n k =
  if n = 0
    then k 0
    else sum (n - 1) (fun r -> k (n + r))

let main () =
  let n = read_int () in
  sum n (fun r -> print_int r)

(*  *)
(* 
let s' (k : int -> unit) =
  let rec sum n (k : int -> unit) =
    if n<=0
      then k 0
      else (sum (n - 1) (fun m -> k (m + n)))
  in sum (read_int ()) k

let () =
  s' (fun r -> print_int r)


let rec sum n =
  if n<=0
    then 0
    else n + sum (n-1)

let () =
  sum (Random.int 0) |> ignore *) *)
