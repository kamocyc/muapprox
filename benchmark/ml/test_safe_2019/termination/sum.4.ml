let rec sum (prev_set_flag_sum_36:bool) (s_prev_sum_n_35:int) (n:int) : 
  int =
  if prev_set_flag_sum_36
  then
    if s_prev_sum_n_35 > n && n >= 0 then () else assert false;
  sum_without_checking_44 prev_set_flag_sum_36 s_prev_sum_n_35 n
and sum_without_checking_44 (_:bool) (_:int) (n:int) : int =
  let set_flag_sum_37 : bool = true
  in
  let s_sum_n_34 : int = n
  in
  if n <= 0
  then
    0
  else
    n + sum set_flag_sum_37 s_sum_n_34 (n - 1)
let u_1603 : int = sum_without_checking_44 false 0 (Random.int 0)
