let succ (_:bool) (_:int) (_:int) (n:int) : int = n + 1
let rec g (x_DO_NOT_CARE_154:bool) (x_DO_NOT_CARE_155:int)
         (x_DO_NOT_CARE_156:int) (r_EXPARAM_85:int) (x_DO_NOT_CARE_151:bool)
         (x_DO_NOT_CARE_152:int) (x_DO_NOT_CARE_153:int)
         (r:(bool -> int -> int -> int -> int)) (prev_set_flag_g_130:bool)
         (s_prev_g_r_EXPARAM_127:int) (s_prev_g_a_129:int) (a:int) : 
  int =
  if prev_set_flag_g_130
  then
    if
      4 + (-2) * s_prev_g_r_EXPARAM_127 > 4 + (-2) * r_EXPARAM_85 &&
      4 + (-2) * r_EXPARAM_85 >= 0
    then
      ()
    else
      assert false;
  g_without_checking_149
    x_DO_NOT_CARE_154 x_DO_NOT_CARE_155 x_DO_NOT_CARE_156 r_EXPARAM_85
    x_DO_NOT_CARE_151 x_DO_NOT_CARE_152 x_DO_NOT_CARE_153 r
    prev_set_flag_g_130 s_prev_g_r_EXPARAM_127 s_prev_g_a_129 a
and g_without_checking_149 (_:bool) (_:int) (_:int) (r_EXPARAM_85:int)
                          (_:bool) (_:int) (_:int)
                          (r:(bool -> int -> int -> int -> int)) (_:bool)
                          (_:int) (_:int) (a:int) : int =
  let set_flag_g_131 : bool = true
  in
  let s_g_a_126 : int = a
  in
  let s_g_r_EXPARAM_124 : int = r_EXPARAM_85
  in
  r
    set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126
    (r set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126 a)
let rec f (set_flag_g_131:bool) (s_g_r_EXPARAM_124:int) (s_g_a_126:int)
         (n:int) : (bool -> int -> int -> int -> int) =
  if n = 0
  then
    succ
  else
    g
      set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126 ((-4) * n + 1)
      set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126
      (f set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126 (n - 1))
let main (_:bool) (_:int) (_:int) (n:int) (set_flag_g_131:bool)
        (s_g_r_EXPARAM_124:int) (s_g_a_126:int) (x:int) : int =
  if n >= 0 && x >= 0
  then
    f
      set_flag_g_131 s_g_r_EXPARAM_124 s_g_a_126 n set_flag_g_131
      s_g_r_EXPARAM_124 s_g_a_126 x
  else
    0
let u_5702 : int = main false 0 0 (Random.int 0) false 0 0 (Random.int 0)
