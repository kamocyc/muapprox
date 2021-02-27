(* プログラムを実行して展開回数を調べるために生成するプログラムの例 *)
exception TooManyRecursions
let upper_limit = 10000
let count_ack = ref 0

let rec sentry m n =
  ((not (n > 0 && m > 0)) || ack m n (fun _ -> true)) && 
  (     (n > 0 && m > 0)  || true)
and ack m n k =
  count_ack := !count_ack + 1;
  if !count_ack > upper_limit then raise TooManyRecursions;
  (m != 0 || k (n + 1)) &&
  (m  = 0 || (
    (n != 0  || ack (m - 1) 1 k) &&
    (n  = 0 || ack m (n - 1) (fun r -> ack (m - 1) r k))
  ))

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
  
  