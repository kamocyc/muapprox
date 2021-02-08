let rec succ (prev_set_flag_succ_89:bool) (s_prev_succ_n_88:int) (n:int) : 
  int =
  if prev_set_flag_succ_89 then assert false;
  succ_without_checking_114 prev_set_flag_succ_89 s_prev_succ_n_88 n
and succ_without_checking_114 (_:bool) (_:int) (n:int) : int =
  let set_flag_succ_90 : bool = true
  in
  let s_succ_n_87 : int = n
  in
  n + 1
let g (_:bool) (_:int) (_:int) (_:bool) (_:int)
     (r:(bool -> int -> int -> int)) (set_flag_succ_90:bool)
     (s_succ_n_87:int) (a:int) : int =
  r set_flag_succ_90 s_succ_n_87 (r set_flag_succ_90 s_succ_n_87 a)
let rec f (set_flag_succ_90:bool) (s_succ_n_87:int) (n:int) : (bool ->
                                                                 int ->
                                                                   int ->
                                                                    int) =
  if n = 0
  then
    succ
  else
    g
      set_flag_succ_90 s_succ_n_87 (0 * n + 0) set_flag_succ_90
      s_succ_n_87 (f set_flag_succ_90 s_succ_n_87 (n - 1))
let main (_:bool) (_:int) (n:int) (set_flag_succ_90:bool)
        (s_succ_n_87:int) (x:int) : int =
  if n >= 0 && x >= 0
  then
    f set_flag_succ_90 s_succ_n_87 n set_flag_succ_90 s_succ_n_87 x
  else
    0
let u_492 : int = main false 0 (Random.int 0) false 0 (Random.int 0)
