let rec f (prev_set_flag_f_42:bool) (s_prev_f_n_41:int) (n:int) : unit =
  if prev_set_flag_f_42
  then
    if (-1) + s_prev_f_n_41 > (-1) + n && (-1) + n >= 0
    then
      ()
    else
      assert false;
  f_without_checking_53 prev_set_flag_f_42 s_prev_f_n_41 n
and f_without_checking_53 (_:bool) (_:int) (n:int) : unit =
  let set_flag_f_43 : bool = true
  in
  let s_f_n_40 : int = n
  in
  let r : int = Random.int 0
  in
  let delta : int = if r > 0 then r else 1 - r
  in
  let n_next : int = n - delta
  in
  (if n_next > 0 then f set_flag_f_43 s_f_n_40 n_next)
let u_1979 : unit = f_without_checking_53 false 0 (Random.int 0)
