let rec foldr (_:bool) (_:int) (_:int) (h_EXPARAM_92:int) (_:bool) (_:int)
             (_:int)
             (h:(bool ->
                   int -> int -> int -> bool -> int -> int -> int -> int))
             (_:bool) (_:int) (_:int) (e:int) (set_flag_sum_167:bool)
             (s_sum_m_162:int) (s_sum_n_163:int) (l:int) : int =
  if l = 0
  then
    e
  else
    h
      set_flag_sum_167 s_sum_m_162 s_sum_n_163 (Random.int 0)
      set_flag_sum_167 s_sum_m_162 s_sum_n_163
      (foldr
        set_flag_sum_167 s_sum_m_162 s_sum_n_163
        (0 * l + (0 * e + (0 * h_EXPARAM_92 + 0))) set_flag_sum_167
        s_sum_m_162 s_sum_n_163 h set_flag_sum_167 s_sum_m_162 s_sum_n_163 
        e set_flag_sum_167 s_sum_m_162 s_sum_n_163 (l - 1))
let rec sum (x_DO_NOT_CARE_180:bool) (x_DO_NOT_CARE_181:int)
           (x_DO_NOT_CARE_182:int) (m:int) (prev_set_flag_sum_166:bool)
           (s_prev_sum_m_164:int) (s_prev_sum_n_165:int) (n:int) : int =
  if prev_set_flag_sum_166 then assert false;
  sum_without_checking_178
    x_DO_NOT_CARE_180 x_DO_NOT_CARE_181 x_DO_NOT_CARE_182 m
    prev_set_flag_sum_166 s_prev_sum_m_164 s_prev_sum_n_165 n
and sum_without_checking_178 (_:bool) (_:int) (_:int) (m:int) (_:bool)
                            (_:int) (_:int) (n:int) : int =
  let set_flag_sum_167 : bool = true
  in
  let s_sum_n_163 : int = n
  in
  let s_sum_m_162 : int = m
  in
  m + n
let main (set_flag_sum_167:bool) (s_sum_m_162:int) (s_sum_n_163:int)
        (():unit) : int =
  let l : int = Random.int 0
  in
  if l >= 0
  then
    foldr
      set_flag_sum_167 s_sum_m_162 s_sum_n_163 0 set_flag_sum_167
      s_sum_m_162 s_sum_n_163 sum set_flag_sum_167 s_sum_m_162
      s_sum_n_163 (Random.int 0) set_flag_sum_167 s_sum_m_162 s_sum_n_163
      l
  else
    0
let u_15503 : int = main false 0 0 ()
