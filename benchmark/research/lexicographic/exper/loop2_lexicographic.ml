(* 必要な再帰回数: n + 2 * m  なので、lexicogprahicでなくてもいい (iter=4で解ける) が、係数が大きすぎてタイムアウトする模様（lexicogprahicだと解ける） *)
let max_count = ref 0
let rec sentry n m =
  f 0 n m (fun _ -> true)
and f i m n k =
  if i > !max_count then max_count := i;
  print_endline @@ string_of_int i;
  print_endline @@ "(" ^ string_of_int m ^ ", " ^ string_of_int n ^ ")";
  (m <= 0 || f (i + 1) (m-1) n k) &&
  (m > 0 || n <= 0 || f (i + 1) (m+1) (n-1) k) &&
  (m > 0 || n > 0 || k false)

let () =
  ignore @@ sentry 80 90 ;
  print_int @@ !max_count
  
