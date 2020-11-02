let rec fib (prev_set_flag_fib_43:bool) (s_prev_fib_n_42:int) (n:int) : 
  int =
  if prev_set_flag_fib_43 then assert false;
  fib_without_checking_52 prev_set_flag_fib_43 s_prev_fib_n_42 n
and fib_without_checking_52 (_:bool) (_:int) (n:int) : int =
  let set_flag_fib_44 : bool = true
  in
  let s_fib_n_41 : int = n
  in
  if n < 2
  then
    1
  else
    fib_without_checking_52 set_flag_fib_44 s_fib_n_41 (n - 1) +
    fib_without_checking_52 set_flag_fib_44 s_fib_n_41 (n - 2)
let main (set_flag_fib_44:bool) (s_fib_n_41:int) (():unit) : int =
  fib set_flag_fib_44 s_fib_n_41 (Random.int 0)
let u_132 : int = main false 0 ()
