let rec f (x_DO_NOT_CARE_88:bool) (x_DO_NOT_CARE_89:int)
         (x_DO_NOT_CARE_90:int) (m:int) (prev_set_flag_f_74:bool)
         (s_prev_f_m_72:int) (s_prev_f_n_73:int) (n:int) : unit =
  if prev_set_flag_f_74
  then
    if
      s_prev_f_m_72 > m && m >= 0 ||
      s_prev_f_m_72 >= m && (s_prev_f_n_73 > n && n >= 0)
    then
      ()
    else
      assert false;
  f_without_checking_86
    x_DO_NOT_CARE_88 x_DO_NOT_CARE_89 x_DO_NOT_CARE_90 m prev_set_flag_f_74
    s_prev_f_m_72 s_prev_f_n_73 n
and f_without_checking_86 (_:bool) (_:int) (_:int) (m:int) (_:bool) (_:int)
                         (_:int) (n:int) : unit =
  let set_flag_f_75 : bool = true
  in
  let s_f_n_71 : int = n
  in
  let s_f_m_70 : int = m
  in
  let r : int = Random.int 0
  in
  if r > 0 && m > 0
  then
    f_without_checking_86
      set_flag_f_75 s_f_m_70 s_f_n_71 (m - 1) set_flag_f_75 s_f_m_70 
      s_f_n_71 n
  else
    (if r <= 0 && n > 0
     then
       f
         set_flag_f_75 s_f_m_70 s_f_n_71 m set_flag_f_75 s_f_m_70 s_f_n_71
         (n - 1))
let main (set_flag_f_75:bool) (s_f_m_70:int) (s_f_n_71:int) (():unit) : 
  unit =
  f_without_checking_86
    set_flag_f_75 s_f_m_70 s_f_n_71 (Random.int 0) set_flag_f_75 s_f_m_70
    s_f_n_71 (Random.int 0)
let u_9045 : unit = main false 0 0 ()
