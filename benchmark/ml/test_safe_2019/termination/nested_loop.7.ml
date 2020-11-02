let rec loop1 (set_flag_loop2_75:bool) (s_loop2_n2_72:int) (n1:int) : 
  int =
  if n1 > 0 then loop1 set_flag_loop2_75 s_loop2_n2_72 (n1 - 1) else 0
let rec loop2 (prev_set_flag_loop2_74:bool) (s_prev_loop2_n2_73:int)
             (n2:int) : int =
  if prev_set_flag_loop2_74
  then
    if s_prev_loop2_n2_73 > n2 && n2 >= 0
    then
      ()
    else
      assert false;
  loop2_without_checking_82
    prev_set_flag_loop2_74 s_prev_loop2_n2_73 n2
and loop2_without_checking_82 (_:bool) (_:int) (n2:int) : int =
  let set_flag_loop2_75 : bool = true
  in
  let s_loop2_n2_72 : int = n2
  in
  if n2 > 0
  then
    loop1 set_flag_loop2_75 s_loop2_n2_72 n2 +
    loop2_without_checking_82
      set_flag_loop2_75 s_loop2_n2_72 (n2 - 1)
  else
    0
let u_5039 : int = loop2 false 0 (Random.int 0)
