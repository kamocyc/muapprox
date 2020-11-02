let succ (_:bool) (_:int) (n:int) : int = n + 1
let g (_:bool) (_:int) (_:int) (_:bool) (_:int)
     (r:(bool -> int -> int -> int)) (set_flag_f_178:bool) (s_f_n_175:int)
     (a:int) : int =
  r set_flag_f_178 s_f_n_175 (r set_flag_f_178 s_f_n_175 a)
let rec f (prev_set_flag_f_177:bool) (s_prev_f_n_176:int) (n:int) : (
                                                                    bool ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  if prev_set_flag_f_177
  then
    if s_prev_f_n_176 > n && n >= 0 then () else assert false;
  f_without_checking_186 prev_set_flag_f_177 s_prev_f_n_176 n
and f_without_checking_186 (_:bool) (_:int) (n:int) : (bool ->
                                                         int ->
                                                           int -> int) =
  let set_flag_f_178 : bool = true
  in
  let s_f_n_175 : int = n
  in
  if n = 0
  then
    succ
  else
    g
      set_flag_f_178 s_f_n_175 (0 * n + 0) set_flag_f_178 s_f_n_175
      (f_without_checking_186 set_flag_f_178 s_f_n_175 (n - 1))
let main (_:bool) (_:int) (n:int) (set_flag_f_178:bool)
        (s_f_n_175:int) (x:int) : int =
  if n >= 0 && x >= 0
  then
    f set_flag_f_178 s_f_n_175 n set_flag_f_178 s_f_n_175 x
  else
    0
let u_12319 : int =
  main false 0 (Random.int 0) false 0 (Random.int 0)
