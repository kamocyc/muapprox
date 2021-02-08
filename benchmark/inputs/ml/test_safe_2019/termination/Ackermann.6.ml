let rec ack (x_DO_NOT_CARE_95:bool) (x_DO_NOT_CARE_96:int)
           (x_DO_NOT_CARE_97:int) (m:int) (prev_set_flag_ack_80:bool)
           (s_prev_ack_m_78:int) (s_prev_ack_n_79:int) (n:int) : int =
  if prev_set_flag_ack_80
  then
    if
      s_prev_ack_m_78 > m && m >= 0 ||
      s_prev_ack_m_78 >= m && (s_prev_ack_n_79 > n && n >= 0)
    then
      ()
    else
      assert false;
  ack_without_checking_93
    x_DO_NOT_CARE_95 x_DO_NOT_CARE_96 x_DO_NOT_CARE_97 m prev_set_flag_ack_80
    s_prev_ack_m_78 s_prev_ack_n_79 n
and ack_without_checking_93 (_:bool) (_:int) (_:int) (m:int) (_:bool) 
                           (_:int) (_:int) (n:int) : int =
  let set_flag_ack_81 : bool = true
  in
  let s_ack_n_77 : int = n
  in
  let s_ack_m_76 : int = m
  in
  if m = 0
  then
    n + 1
  else
    if n = 0
    then
      ack_without_checking_93
        set_flag_ack_81 s_ack_m_76 s_ack_n_77 (m - 1) set_flag_ack_81
        s_ack_m_76 s_ack_n_77 1
    else
      ack_without_checking_93
        set_flag_ack_81 s_ack_m_76 s_ack_n_77 (m - 1) set_flag_ack_81
        s_ack_m_76 s_ack_n_77
        (ack_without_checking_93
          set_flag_ack_81 s_ack_m_76 s_ack_n_77 m set_flag_ack_81 s_ack_m_76
          s_ack_n_77 (n - 1))
let main (set_flag_ack_81:bool) (s_ack_m_76:int) (s_ack_n_77:int) (():unit) : 
  int =
  let m : int = Random.int 0
  in
  let n : int = Random.int 0
  in
  if n > 0 && m > 0
  then
    ack
      set_flag_ack_81 s_ack_m_76 s_ack_n_77 m set_flag_ack_81 s_ack_m_76
      s_ack_n_77 n
  else
    0
let u_11049 : int = main false 0 0 ()
