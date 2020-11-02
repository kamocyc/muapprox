let rec mc91 (prev_set_flag_mc91_39:bool) (s_prev_mc91_n_38:int) (n:int) : 
  int =
  if prev_set_flag_mc91_39
  then
    if 111 + -s_prev_mc91_n_38 > 111 + -n && 111 + -n >= 0
    then
      ()
    else
      assert false;
  mc91_without_checking_48 prev_set_flag_mc91_39 s_prev_mc91_n_38 n
and mc91_without_checking_48 (_:bool) (_:int) (n:int) : int =
  let set_flag_mc91_40 : bool = true
  in
  let s_mc91_n_37 : int = n
  in
  if n > 100
  then
    n - 10
  else
    mc91
      set_flag_mc91_40 s_mc91_n_37
      (mc91_without_checking_48 set_flag_mc91_40 s_mc91_n_37 (n + 11))
let main (set_flag_mc91_40:bool) (s_mc91_n_37:int) (():unit) : int =
  mc91_without_checking_48 set_flag_mc91_40 s_mc91_n_37 (Random.int 0)
let u_2866 : int = main false 0 ()
