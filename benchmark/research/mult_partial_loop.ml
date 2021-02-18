
let read_int () = Random.int 1000

let rec mult n m k =
  if m <= 0
  then k 0
  else mult n (m - 1) (fun r -> k (n + r))

let rec loop nf k =
  let m = read_int () in
  nf m (fun n ->
    if n > 0 then loop (fun _ f -> f (n - 1)) k
    else k 0
  )

let () =
  let n = read_int () in
  loop (mult n) (fun r -> print_int r)
