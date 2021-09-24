let make_arrray k = k (fun i k' -> k' 0)
let update ar i x k =
  k (fun j k' -> if j = i then k' x else ar j k')
let pred ar k = ar 0 (fun x -> update ar 0 (x - 1) k)
let check f k =
  f 0 (fun x ->
    if x > 0 then k 1 else k 0
  )
let rec loop1 ar_n1 k =
  check ar_n1 (fun b ->
    if b = 1 then pred ar_n1 (fun ar_n1_2 -> loop1 ar_n1_2 k) else k 0
  )


let rec loop1 n1 k = if n1 > 0 then loop1 (n1-1) k else k 0
let rec loop2 n2 k = if n2 > 0 then loop1 n2 (fun r1 -> loop2 (n2-1) (fun r2 -> k (r1 + r2))) else k 0

let () =
  let i = read_int () in
  loop2 i (fun r -> print_int r)