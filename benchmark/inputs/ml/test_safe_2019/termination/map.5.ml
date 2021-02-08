let rec map (_:bool) (_:int) (_:int) (_:int) (f_EXPARAM_121:int) (_:bool)
           (_:int) (_:int) (_:int)
           (f:(bool -> int -> int -> int -> int -> int))
           (set_flag_compose_204:bool) (s_compose_f_EXPARAM_193:int)
           (s_compose_g_EXPARAM_195:int) (s_compose_x_197:int) (xs:int) : 
  int =
  if xs = 0
  then
    0
  else
    f
      set_flag_compose_204 s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195
      s_compose_x_197 (Random.int 0)
    +
    map
      set_flag_compose_204 s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195
      s_compose_x_197 (0 * xs + (0 * f_EXPARAM_121 + 0)) set_flag_compose_204
      s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195 s_compose_x_197 
      f set_flag_compose_204 s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195
      s_compose_x_197 (xs - 1)
let rec compose (x_DO_NOT_CARE_243:bool) (x_DO_NOT_CARE_244:int)
               (x_DO_NOT_CARE_245:int) (x_DO_NOT_CARE_246:int)
               (f_EXPARAM_117:int) (x_DO_NOT_CARE_239:bool)
               (x_DO_NOT_CARE_240:int) (x_DO_NOT_CARE_241:int)
               (x_DO_NOT_CARE_242:int)
               (f:(bool -> int -> int -> int -> int -> int))
               (x_DO_NOT_CARE_235:bool) (x_DO_NOT_CARE_236:int)
               (x_DO_NOT_CARE_237:int) (x_DO_NOT_CARE_238:int)
               (g_EXPARAM_118:int) (x_DO_NOT_CARE_231:bool)
               (x_DO_NOT_CARE_232:int) (x_DO_NOT_CARE_233:int)
               (x_DO_NOT_CARE_234:int)
               (g:(bool -> int -> int -> int -> int -> int))
               (prev_set_flag_compose_203:bool)
               (s_prev_compose_f_EXPARAM_198:int)
               (s_prev_compose_g_EXPARAM_200:int) (s_prev_compose_x_202:int)
               (x:int) : int =
  if prev_set_flag_compose_203 then assert false;
  compose_without_checking_229
    x_DO_NOT_CARE_243 x_DO_NOT_CARE_244 x_DO_NOT_CARE_245
    x_DO_NOT_CARE_246 f_EXPARAM_117 x_DO_NOT_CARE_239 x_DO_NOT_CARE_240
    x_DO_NOT_CARE_241 x_DO_NOT_CARE_242 f x_DO_NOT_CARE_235
    x_DO_NOT_CARE_236 x_DO_NOT_CARE_237 x_DO_NOT_CARE_238 g_EXPARAM_118
    x_DO_NOT_CARE_231 x_DO_NOT_CARE_232 x_DO_NOT_CARE_233
    x_DO_NOT_CARE_234 g prev_set_flag_compose_203
    s_prev_compose_f_EXPARAM_198 s_prev_compose_g_EXPARAM_200
    s_prev_compose_x_202 x
and compose_without_checking_229 (_:bool) (_:int) (_:int) (_:int)
                                (f_EXPARAM_117:int) (_:bool) (_:int)
                                (_:int) (_:int)
                                (f:(bool ->
                                      int -> int -> int -> int -> int))
                                (_:bool) (_:int) (_:int) (_:int)
                                (g_EXPARAM_118:int) (_:bool) (_:int)
                                (_:int) (_:int)
                                (g:(bool ->
                                      int -> int -> int -> int -> int))
                                (_:bool) (_:int) (_:int) (_:int) (x:int) : 
  int =
  let set_flag_compose_204 : bool = true
  in
  let s_compose_x_197 : int = x
  in
  let s_compose_g_EXPARAM_195 : int = g_EXPARAM_118
  in
  let s_compose_f_EXPARAM_193 : int = f_EXPARAM_117
  in
  f
    set_flag_compose_204 s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195
    s_compose_x_197
    (g
      set_flag_compose_204 s_compose_f_EXPARAM_193
      s_compose_g_EXPARAM_195 s_compose_x_197 x)
let add (_:bool) (_:int) (_:int) (_:int) (x:int) (_:bool) (_:int) (_:int)
       (_:int) (y:int) : int = x + y
let main (set_flag_compose_204:bool) (s_compose_f_EXPARAM_193:int)
        (s_compose_g_EXPARAM_195:int) (s_compose_x_197:int) (():unit) : 
  int =
  let l : int = Random.int 0
  in
  if l >= 0
  then
    map
      set_flag_compose_204 s_compose_f_EXPARAM_193
      s_compose_g_EXPARAM_195 s_compose_x_197 0 set_flag_compose_204
      s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195 s_compose_x_197
      (compose
        set_flag_compose_204 s_compose_f_EXPARAM_193
        s_compose_g_EXPARAM_195 s_compose_x_197 0 set_flag_compose_204
        s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195 s_compose_x_197
        (add
          set_flag_compose_204 s_compose_f_EXPARAM_193
          s_compose_g_EXPARAM_195 s_compose_x_197 1)
        set_flag_compose_204 s_compose_f_EXPARAM_193
        s_compose_g_EXPARAM_195 s_compose_x_197 0 set_flag_compose_204
        s_compose_f_EXPARAM_193 s_compose_g_EXPARAM_195 s_compose_x_197
        (add
          set_flag_compose_204 s_compose_f_EXPARAM_193
          s_compose_g_EXPARAM_195 s_compose_x_197 2))
      set_flag_compose_204 s_compose_f_EXPARAM_193
      s_compose_g_EXPARAM_195 s_compose_x_197 l
  else
    0
let u_15314 : int = main false 0 0 0 ()
