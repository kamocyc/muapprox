(* プログラムを実行して展開回数を調べるために生成するプログラムの例 *)
exception TooManyRecursions
let upper_limit = 10000
let count_ack = ref 0

let rec sentry n m =
  f n m (fun _ -> true)
and f m n k =
  count_ack := !count_ack + 1;
  if !count_ack > upper_limit then raise TooManyRecursions;
  (m <= 0 || f (m-1) n k) &&
  (n <= 0 || f (m+1) (n-1) k) &&
  k false


let () = 
  for total = 0 to 5 do
    for i = 0 to total do
      count_ack := 0;
      (try
        ignore @@ sentry i (total - i);
      with
        TooManyRecursions -> ());
      print_endline @@ "(" ^ string_of_int i ^ ", " ^ string_of_int (total - i) ^ "): " ^ string_of_int !count_ack;
    done
  done
  
  
  
(* 
let () = 
  let n = read_int () in
  let m = read_int () in
  ignore @@ sentry n m *)