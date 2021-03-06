let rec loop1 (prev_set_flag_loop1_50:bool) (s_prev_loop1_n1_49:int) (n1:int) : 
  int =
  if prev_set_flag_loop1_50 then assert false;
  loop1_without_checking_64 prev_set_flag_loop1_50 s_prev_loop1_n1_49 n1
and loop1_without_checking_64 (_:bool) (_:int) (n1:int) : int =
  let set_flag_loop1_51 : bool = true
  in
  let s_loop1_n1_48 : int = n1
  in
  if n1 > 0
  then
    loop1_without_checking_64 set_flag_loop1_51 s_loop1_n1_48 (n1 - 1)
  else
    0
let rec loop2 (set_flag_loop1_51:bool) (s_loop1_n1_48:int) (n2:int) : 
  int =
  if n2 > 0
  then
    loop1 set_flag_loop1_51 s_loop1_n1_48 n2 +
    loop2 set_flag_loop1_51 s_loop1_n1_48 (n2 - 1)
  else
    0
let u_167 : int = loop2 false 0 (Random.int 0)
