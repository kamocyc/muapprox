let rec map (x_DO_NOT_CARE_174:bool) (x_DO_NOT_CARE_175:int)
           (x_DO_NOT_CARE_176:int) (f_EXPARAM_121:int)
           (x_DO_NOT_CARE_171:bool) (x_DO_NOT_CARE_172:int)
           (x_DO_NOT_CARE_173:int) (f:(bool -> int -> int -> int -> int))
           (prev_set_flag_map_133:bool) (s_prev_map_f_EXPARAM_130:int)
           (s_prev_map_xs_132:int) (xs:int) : int =
  if prev_set_flag_map_133 then assert false;
  map_without_checking_169
    x_DO_NOT_CARE_174 x_DO_NOT_CARE_175 x_DO_NOT_CARE_176 f_EXPARAM_121
    x_DO_NOT_CARE_171 x_DO_NOT_CARE_172 x_DO_NOT_CARE_173 f
    prev_set_flag_map_133 s_prev_map_f_EXPARAM_130 s_prev_map_xs_132 
    xs
and map_without_checking_169 (_:bool) (_:int) (_:int) (f_EXPARAM_121:int)
                            (_:bool) (_:int) (_:int)
                            (f:(bool -> int -> int -> int -> int))
                            (_:bool) (_:int) (_:int) (xs:int) : int =
  let set_flag_map_134 : bool = true
  in
  let s_map_xs_129 : int = xs
  in
  let s_map_f_EXPARAM_127 : int = f_EXPARAM_121
  in
  if xs = 0
  then
    0
  else
    f set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 (Random.int 0) +
    map_without_checking_169
      set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129
      (0 * xs + (0 * f_EXPARAM_121 + 0)) set_flag_map_134
      s_map_f_EXPARAM_127 s_map_xs_129 f set_flag_map_134
      s_map_f_EXPARAM_127 s_map_xs_129 (xs - 1)
let compose (_:bool) (_:int) (_:int) (_:int) (_:bool) (_:int) (_:int)
           (f:(bool -> int -> int -> int -> int)) (_:bool) (_:int)
           (_:int) (_:int) (_:bool) (_:int) (_:int)
           (g:(bool -> int -> int -> int -> int)) (set_flag_map_134:bool)
           (s_map_f_EXPARAM_127:int) (s_map_xs_129:int) (x:int) : int =
  f
    set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129
    (g set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 x)
let add (_:bool) (_:int) (_:int) (x:int) (_:bool) (_:int) (_:int) (y:int) : 
  int = x + y
let main (set_flag_map_134:bool) (s_map_f_EXPARAM_127:int)
        (s_map_xs_129:int) (():unit) : int =
  let l : int = Random.int 0
  in
  if l >= 0
  then
    map
      set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 0
      set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129
      (compose
        set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 0
        set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129
        (add set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 1)
        set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 0
        set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129
        (add set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 2))
      set_flag_map_134 s_map_f_EXPARAM_127 s_map_xs_129 l
  else
    0
let u_1323 : int = main false 0 0 ()
