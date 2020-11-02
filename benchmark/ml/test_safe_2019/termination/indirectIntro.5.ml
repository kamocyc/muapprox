let rec app (x_DO_NOT_CARE_172:bool) (x_DO_NOT_CARE_173:int)
           (x_DO_NOT_CARE_174:int) (x_DO_NOT_CARE_175:int) (i:int)
           (x_DO_NOT_CARE_168:bool) (x_DO_NOT_CARE_169:int)
           (x_DO_NOT_CARE_170:int) (x_DO_NOT_CARE_171:int)
           (h_EXPARAM_112:int) (x_DO_NOT_CARE_164:bool)
           (x_DO_NOT_CARE_165:int) (x_DO_NOT_CARE_166:int)
           (x_DO_NOT_CARE_167:int)
           (h:(bool ->
                 int ->
                   int ->
                     int -> int -> bool -> int -> int -> int -> unit -> unit))
           (x_DO_NOT_CARE_160:bool) (x_DO_NOT_CARE_161:int)
           (x_DO_NOT_CARE_162:int) (x_DO_NOT_CARE_163:int) (v:int)
           (prev_set_flag_app_129:bool) (s_prev_app_i_124:int)
           (s_prev_app_h_EXPARAM_125:int) (s_prev_app_v_127:int) (u:unit) : 
  unit =
  if prev_set_flag_app_129
  then
    if
      s_prev_app_v_127 > v && v >= 0 ||
      s_prev_app_v_127 >= v && (1 + s_prev_app_i_124 > 1 + i && 1 + i >= 0)
    then
      ()
    else
      assert false;
  app_without_checking_158
    x_DO_NOT_CARE_172 x_DO_NOT_CARE_173 x_DO_NOT_CARE_174 x_DO_NOT_CARE_175 
    i x_DO_NOT_CARE_168 x_DO_NOT_CARE_169 x_DO_NOT_CARE_170 x_DO_NOT_CARE_171
    h_EXPARAM_112 x_DO_NOT_CARE_164 x_DO_NOT_CARE_165 x_DO_NOT_CARE_166
    x_DO_NOT_CARE_167 h x_DO_NOT_CARE_160 x_DO_NOT_CARE_161 x_DO_NOT_CARE_162
    x_DO_NOT_CARE_163 v prev_set_flag_app_129 s_prev_app_i_124
    s_prev_app_h_EXPARAM_125 s_prev_app_v_127 u
and app_without_checking_158 (_:bool) (_:int) (_:int) (_:int) (i:int)
                            (_:bool) (_:int) (_:int) (_:int)
                            (h_EXPARAM_112:int) (_:bool) (_:int) (_:int)
                            (_:int)
                            (h:(bool ->
                                  int ->
                                    int ->
                                      int ->
                                        int ->
                                          bool ->
                                            int -> int -> int -> unit -> unit))
                            (_:bool) (_:int) (_:int) (_:int) (v:int) 
                            (_:bool) (_:int) (_:int) (_:int) (u:unit) : 
  unit =
  let set_flag_app_130 : bool = true
  in
  let s_app_v_122 : int = v
  in
  let s_app_h_EXPARAM_120 : int = h_EXPARAM_112
  in
  let s_app_i_119 : int = i
  in
  if i >= 0
  then
    app_without_checking_158
      set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 (i - 1)
      set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122
      (0 * v + (0 * h_EXPARAM_112 + (0 * i + 0))) set_flag_app_130
      s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 h set_flag_app_130
      s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 v set_flag_app_130
      s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 u
  else
    h
      set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 v
      set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122 u
let g (_:bool) (_:int) (_:int) (_:int) (():unit) : unit = ()
let rec f (set_flag_app_130:bool) (s_app_i_119:int) (s_app_h_EXPARAM_120:int)
         (s_app_v_122:int) (x:int) : (bool ->
                                        int -> int -> int -> unit -> unit) =
  if x > 0
  then
    app
      set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122
      (Random.int 0) set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120
      s_app_v_122 (0 * x + 0) set_flag_app_130 s_app_i_119
      s_app_h_EXPARAM_120 s_app_v_122 f set_flag_app_130 s_app_i_119
      s_app_h_EXPARAM_120 s_app_v_122 (x - 1)
  else
    g
let main (set_flag_app_130:bool) (s_app_i_119:int) (s_app_h_EXPARAM_120:int)
        (s_app_v_122:int) (():unit) : unit =
  f
    set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120 s_app_v_122
    (Random.int 0) set_flag_app_130 s_app_i_119 s_app_h_EXPARAM_120
    s_app_v_122 ()
let u_29976 : unit = main false 0 0 0 ()
