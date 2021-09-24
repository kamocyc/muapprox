let rec app (i:int) h (v : int) (u : unit) k =
  print_endline @@ "(" ^ string_of_int v ^ ", " ^ string_of_int i ^ ")";
  if i>=0 then app (i-1) h v u k else (h v u k : unit)

let g (u : unit) k = k ()

let rec f (x : int) y k =
  if x > 0 then
    app (read_int()) f (x-1) y k
  else
    g y k
  
let () =
  f (read_int ()) () (fun r -> ())