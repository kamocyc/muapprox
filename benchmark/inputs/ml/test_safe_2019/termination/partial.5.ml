let gt (_:bool) (_:int) (_:int) (lb:int) (_:bool) (_:int) (_:int) (n:int) : 
  bool = n > lb
let rec f (x_DO_NOT_CARE_131:bool) (x_DO_NOT_CARE_132:int)
         (x_DO_NOT_CARE_133:int) (x:int) (x_DO_NOT_CARE_128:bool)
         (x_DO_NOT_CARE_129:int) (x_DO_NOT_CARE_130:int) (p_EXPARAM_61:int)
         (prev_set_flag_f_114:bool) (s_prev_f_x_111:int)
         (s_prev_f_p_EXPARAM_112:int) (p:(bool -> int -> int -> int -> bool)) : 
  unit =
  if prev_set_flag_f_114
  then
    if s_prev_f_x_111 > x && x >= 0 then () else assert false;
  f_without_checking_126
    x_DO_NOT_CARE_131 x_DO_NOT_CARE_132 x_DO_NOT_CARE_133 x
    x_DO_NOT_CARE_128 x_DO_NOT_CARE_129 x_DO_NOT_CARE_130
    p_EXPARAM_61 prev_set_flag_f_114 s_prev_f_x_111
    s_prev_f_p_EXPARAM_112 p
and f_without_checking_126 (_:bool) (_:int) (_:int) (x:int) (_:bool)
                          (_:int) (_:int) (p_EXPARAM_61:int) (_:bool)
                          (_:int) (_:int)
                          (p:(bool -> int -> int -> int -> bool)) : unit =
  let set_flag_f_115 : bool = true
  in
  let s_f_p_EXPARAM_109 : int = p_EXPARAM_61
  in
  let s_f_x_108 : int = x
  in
  (if p set_flag_f_115 s_f_x_108 s_f_p_EXPARAM_109 x
   then
     f
       set_flag_f_115 s_f_x_108 s_f_p_EXPARAM_109 (x - 1)
       set_flag_f_115 s_f_x_108 s_f_p_EXPARAM_109
       (0 * p_EXPARAM_61 + (0 * x + 0)) set_flag_f_115 s_f_x_108
       s_f_p_EXPARAM_109 p)
let u_9381 : unit =
  f_without_checking_126
    false 0 0 (Random.int 0) false 0 0 0 false 0 0 (gt false 0 0 0)
