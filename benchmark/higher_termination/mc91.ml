let rec mc91 n k =
  if n > 100 then
    k (n - 10)
  else
    mc91 (n + 11) (fun r -> mc91 r k)

let () = 
  mc91 (read_int ()) (fun r -> print_int @@ r)
