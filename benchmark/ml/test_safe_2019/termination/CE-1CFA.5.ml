let id (_:bool) (_:int) (_:int) (_:int) (x:int) : int = x
let rec omega (set_flag_f_172:bool) (s_f_x_EXPARAM_161:int)
             (s_f_y_EXPARAM_163:int) (s_f_z_165:int) (x:int) : int =
  omega set_flag_f_172 s_f_x_EXPARAM_161 s_f_y_EXPARAM_163 s_f_z_165 x
let rec f (x_DO_NOT_CARE_201:bool) (x_DO_NOT_CARE_202:int)
         (x_DO_NOT_CARE_203:int) (x_DO_NOT_CARE_204:int) (x_EXPARAM_73:int)
         (x_DO_NOT_CARE_197:bool) (x_DO_NOT_CARE_198:int)
         (x_DO_NOT_CARE_199:int) (x_DO_NOT_CARE_200:int)
         (x:(bool -> int -> int -> int -> int -> int))
         (x_DO_NOT_CARE_193:bool) (x_DO_NOT_CARE_194:int)
         (x_DO_NOT_CARE_195:int) (x_DO_NOT_CARE_196:int) (y_EXPARAM_74:int)
         (x_DO_NOT_CARE_189:bool) (x_DO_NOT_CARE_190:int)
         (x_DO_NOT_CARE_191:int) (x_DO_NOT_CARE_192:int)
         (y:(bool -> int -> int -> int -> int -> int))
         (prev_set_flag_f_171:bool) (s_prev_f_x_EXPARAM_166:int)
         (s_prev_f_y_EXPARAM_168:int) (s_prev_f_z_170:int) (z:int) : 
  int =
  if prev_set_flag_f_171 then assert false;
  f_without_checking_187
    x_DO_NOT_CARE_201 x_DO_NOT_CARE_202 x_DO_NOT_CARE_203
    x_DO_NOT_CARE_204 x_EXPARAM_73 x_DO_NOT_CARE_197 x_DO_NOT_CARE_198
    x_DO_NOT_CARE_199 x_DO_NOT_CARE_200 x x_DO_NOT_CARE_193
    x_DO_NOT_CARE_194 x_DO_NOT_CARE_195 x_DO_NOT_CARE_196 y_EXPARAM_74
    x_DO_NOT_CARE_189 x_DO_NOT_CARE_190 x_DO_NOT_CARE_191
    x_DO_NOT_CARE_192 y prev_set_flag_f_171 s_prev_f_x_EXPARAM_166
    s_prev_f_y_EXPARAM_168 s_prev_f_z_170 z
and f_without_checking_187 (_:bool) (_:int) (_:int) (_:int)
                          (x_EXPARAM_73:int) (_:bool) (_:int) (_:int)
                          (_:int)
                          (_:(bool -> int -> int -> int -> int -> int))
                          (_:bool) (_:int) (_:int) (_:int)
                          (y_EXPARAM_74:int) (_:bool) (_:int) (_:int)
                          (_:int)
                          (y:(bool -> int -> int -> int -> int -> int))
                          (_:bool) (_:int) (_:int) (_:int) (z:int) : 
  int =
  let set_flag_f_172 : bool = true
  in
  let s_f_z_165 : int = z
  in
  let s_f_y_EXPARAM_163 : int = y_EXPARAM_74
  in
  let s_f_x_EXPARAM_161 : int = x_EXPARAM_73
  in
  y set_flag_f_172 s_f_x_EXPARAM_161 s_f_y_EXPARAM_163 s_f_z_165 z
let u_6960 : int =
  f_without_checking_187
    false 0 0 0 0 false 0 0 0
    (f false 0 0 0 0 false 0 0 0 id false 0 0 0 0 false 0 0 0 omega)
    false 0 0 0 0 false 0 0 0 id false 0 0 0 1
