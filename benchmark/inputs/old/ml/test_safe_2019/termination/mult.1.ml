let rec mult (x_DO_NOT_CARE_65:bool) (x_DO_NOT_CARE_66:int)
            (x_DO_NOT_CARE_67:int) (m:int) (prev_set_flag_mult_51:bool)
            (s_prev_mult_m_49:int) (s_prev_mult_n_50:int) (n:int) : int =
  if prev_set_flag_mult_51 then assert false;
  mult_without_checking_63
    x_DO_NOT_CARE_65 x_DO_NOT_CARE_66 x_DO_NOT_CARE_67 m
    prev_set_flag_mult_51 s_prev_mult_m_49 s_prev_mult_n_50 n
and mult_without_checking_63 (_:bool) (_:int) (_:int) (m:int) (_:bool)
                            (_:int) (_:int) (n:int) : int =
  let set_flag_mult_52 : bool = true
  in
  let s_mult_n_48 : int = n
  in
  let s_mult_m_47 : int = m
  in
  if m > 0
  then
    n +
    mult_without_checking_63
      set_flag_mult_52 s_mult_m_47 s_mult_n_48 (m - 1) set_flag_mult_52
      s_mult_m_47 s_mult_n_48 n
  else
    0
let m : int = Random.int 0
let n : int = Random.int 0
let u_230 : int = if m > 0 then mult false 0 0 m false 0 0 n else 0
