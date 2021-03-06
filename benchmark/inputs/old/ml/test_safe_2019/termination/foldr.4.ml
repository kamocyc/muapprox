let rec foldr (x_DO_NOT_CARE_141:bool) (x_DO_NOT_CARE_142:int)
             (x_DO_NOT_CARE_143:int) (x_DO_NOT_CARE_144:int)
             (h_EXPARAM_92:int) (x_DO_NOT_CARE_137:bool)
             (x_DO_NOT_CARE_138:int) (x_DO_NOT_CARE_139:int)
             (x_DO_NOT_CARE_140:int)
             (h:(bool ->
                   int ->
                     int ->
                       int -> int -> bool -> int -> int -> int -> int -> int))
             (x_DO_NOT_CARE_133:bool) (x_DO_NOT_CARE_134:int)
             (x_DO_NOT_CARE_135:int) (x_DO_NOT_CARE_136:int) (e:int)
             (prev_set_flag_foldr_107:bool) (s_prev_foldr_h_EXPARAM_103:int)
             (s_prev_foldr_e_105:int) (s_prev_foldr_l_106:int) (l:int) : 
  int =
  if prev_set_flag_foldr_107
  then
    if s_prev_foldr_l_106 > l && l >= 0 then () else assert false;
  foldr_without_checking_131
    x_DO_NOT_CARE_141 x_DO_NOT_CARE_142 x_DO_NOT_CARE_143
    x_DO_NOT_CARE_144 h_EXPARAM_92 x_DO_NOT_CARE_137
    x_DO_NOT_CARE_138 x_DO_NOT_CARE_139 x_DO_NOT_CARE_140 h
    x_DO_NOT_CARE_133 x_DO_NOT_CARE_134 x_DO_NOT_CARE_135
    x_DO_NOT_CARE_136 e prev_set_flag_foldr_107
    s_prev_foldr_h_EXPARAM_103 s_prev_foldr_e_105 s_prev_foldr_l_106
    l
and foldr_without_checking_131 (_:bool) (_:int) (_:int) (_:int)
                              (h_EXPARAM_92:int) (_:bool) (_:int)
                              (_:int) (_:int)
                              (h:(bool ->
                                    int ->
                                      int ->
                                        int ->
                                          int ->
                                            bool ->
                                              int ->
                                                int ->
                                                  int -> int -> int))
                              (_:bool) (_:int) (_:int) (_:int)
                              (e:int) (_:bool) (_:int) (_:int)
                              (_:int) (l:int) : int =
  let set_flag_foldr_108 : bool = true
  in
  let s_foldr_l_102 : int = l
  in
  let s_foldr_e_101 : int = e
  in
  let s_foldr_h_EXPARAM_99 : int = h_EXPARAM_92
  in
  if l = 0
  then
    e
  else
    h
      set_flag_foldr_108 s_foldr_h_EXPARAM_99 s_foldr_e_101
      s_foldr_l_102 (Random.int 0) set_flag_foldr_108
      s_foldr_h_EXPARAM_99 s_foldr_e_101 s_foldr_l_102
      (foldr
        set_flag_foldr_108 s_foldr_h_EXPARAM_99 s_foldr_e_101
        s_foldr_l_102 (0 * l + (0 * e + (0 * h_EXPARAM_92 + 0)))
        set_flag_foldr_108 s_foldr_h_EXPARAM_99 s_foldr_e_101
        s_foldr_l_102 h set_flag_foldr_108 s_foldr_h_EXPARAM_99
        s_foldr_e_101 s_foldr_l_102 e set_flag_foldr_108
        s_foldr_h_EXPARAM_99 s_foldr_e_101 s_foldr_l_102 (l - 1))
let sum (_:bool) (_:int) (_:int) (_:int) (m:int) (_:bool) (_:int)
       (_:int) (_:int) (n:int) : int = m + n
let main (set_flag_foldr_108:bool) (s_foldr_h_EXPARAM_99:int)
        (s_foldr_e_101:int) (s_foldr_l_102:int) (():unit) : int =
  let l : int = Random.int 0
  in
  if l >= 0
  then
    foldr_without_checking_131
      set_flag_foldr_108 s_foldr_h_EXPARAM_99 s_foldr_e_101
      s_foldr_l_102 0 set_flag_foldr_108 s_foldr_h_EXPARAM_99
      s_foldr_e_101 s_foldr_l_102 sum set_flag_foldr_108
      s_foldr_h_EXPARAM_99 s_foldr_e_101 s_foldr_l_102 (Random.int 0)
      set_flag_foldr_108 s_foldr_h_EXPARAM_99 s_foldr_e_101
      s_foldr_l_102 l
  else
    0
let u_11638 : int = main false 0 0 0 ()
