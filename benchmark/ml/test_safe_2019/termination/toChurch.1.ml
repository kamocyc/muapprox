let rec compose (x_DO_NOT_CARE_197:bool) (x_DO_NOT_CARE_198:int)
               (x_DO_NOT_CARE_199:int) (x_DO_NOT_CARE_200:int)
               (f_EXPARAM_128:int) (x_DO_NOT_CARE_193:bool)
               (x_DO_NOT_CARE_194:int) (x_DO_NOT_CARE_195:int)
               (x_DO_NOT_CARE_196:int)
               (f:(bool -> int -> int -> int -> int -> int))
               (x_DO_NOT_CARE_189:bool) (x_DO_NOT_CARE_190:int)
               (x_DO_NOT_CARE_191:int) (x_DO_NOT_CARE_192:int)
               (g_EXPARAM_129:int) (x_DO_NOT_CARE_185:bool)
               (x_DO_NOT_CARE_186:int) (x_DO_NOT_CARE_187:int)
               (x_DO_NOT_CARE_188:int)
               (g:(bool -> int -> int -> int -> int -> int))
               (prev_set_flag_compose_142:bool)
               (s_prev_compose_f_EXPARAM_137:int)
               (s_prev_compose_g_EXPARAM_139:int) (s_prev_compose_x_141:int)
               (x:int) : int =
  if prev_set_flag_compose_142 then assert false;
  compose_without_checking_183
    x_DO_NOT_CARE_197 x_DO_NOT_CARE_198 x_DO_NOT_CARE_199
    x_DO_NOT_CARE_200 f_EXPARAM_128 x_DO_NOT_CARE_193 x_DO_NOT_CARE_194
    x_DO_NOT_CARE_195 x_DO_NOT_CARE_196 f x_DO_NOT_CARE_189
    x_DO_NOT_CARE_190 x_DO_NOT_CARE_191 x_DO_NOT_CARE_192 g_EXPARAM_129
    x_DO_NOT_CARE_185 x_DO_NOT_CARE_186 x_DO_NOT_CARE_187
    x_DO_NOT_CARE_188 g prev_set_flag_compose_142
    s_prev_compose_f_EXPARAM_137 s_prev_compose_g_EXPARAM_139
    s_prev_compose_x_141 x
and compose_without_checking_183 (_:bool) (_:int) (_:int) (_:int)
                                (f_EXPARAM_128:int) (_:bool) (_:int)
                                (_:int) (_:int)
                                (f:(bool ->
                                      int -> int -> int -> int -> int))
                                (_:bool) (_:int) (_:int) (_:int)
                                (g_EXPARAM_129:int) (_:bool) (_:int)
                                (_:int) (_:int)
                                (g:(bool ->
                                      int -> int -> int -> int -> int))
                                (_:bool) (_:int) (_:int) (_:int) (x:int) : 
  int =
  let set_flag_compose_143 : bool = true
  in
  let s_compose_x_136 : int = x
  in
  let s_compose_g_EXPARAM_134 : int = g_EXPARAM_129
  in
  let s_compose_f_EXPARAM_132 : int = f_EXPARAM_128
  in
  f
    set_flag_compose_143 s_compose_f_EXPARAM_132 s_compose_g_EXPARAM_134
    s_compose_x_136
    (g
      set_flag_compose_143 s_compose_f_EXPARAM_132
      s_compose_g_EXPARAM_134 s_compose_x_136 x)
let id (_:bool) (_:int) (_:int) (_:int) (x:int) : int = x
let succ (_:bool) (_:int) (_:int) (_:int) (x:int) : int = x + 1
let rec toChurch (_:bool) (_:int) (_:int) (_:int) (n:int) (_:bool)
                (_:int) (_:int) (_:int) (f_EXPARAM_114:int)
                (set_flag_compose_143:bool) (s_compose_f_EXPARAM_132:int)
                (s_compose_g_EXPARAM_134:int) (s_compose_x_136:int)
                (f:(bool -> int -> int -> int -> int -> int)) : (bool ->
                                                                   int ->
                                                                    int ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  if n = 0
  then
    id
  else
    compose
      set_flag_compose_143 s_compose_f_EXPARAM_132
      s_compose_g_EXPARAM_134 s_compose_x_136
      (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_compose_143
      s_compose_f_EXPARAM_132 s_compose_g_EXPARAM_134 s_compose_x_136 
      f set_flag_compose_143 s_compose_f_EXPARAM_132
      s_compose_g_EXPARAM_134 s_compose_x_136
      (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_compose_143
      s_compose_f_EXPARAM_132 s_compose_g_EXPARAM_134 s_compose_x_136
      (toChurch
        set_flag_compose_143 s_compose_f_EXPARAM_132
        s_compose_g_EXPARAM_134 s_compose_x_136 (n - 1)
        set_flag_compose_143 s_compose_f_EXPARAM_132
        s_compose_g_EXPARAM_134 s_compose_x_136
        (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_compose_143
        s_compose_f_EXPARAM_132 s_compose_g_EXPARAM_134 s_compose_x_136 
        f)
let main (set_flag_compose_143:bool) (s_compose_f_EXPARAM_132:int)
        (s_compose_g_EXPARAM_134:int) (s_compose_x_136:int) (():unit) : 
  unit =
  let x : int = Random.int 0
  in
  (if x >= 0
   then
     let tos : (bool -> int -> int -> int -> int -> int) =
       toChurch
         set_flag_compose_143 s_compose_f_EXPARAM_132
         s_compose_g_EXPARAM_134 s_compose_x_136 x set_flag_compose_143
         s_compose_f_EXPARAM_132 s_compose_g_EXPARAM_134 s_compose_x_136
         0 set_flag_compose_143 s_compose_f_EXPARAM_132
         s_compose_g_EXPARAM_134 s_compose_x_136 succ
     in
     ())
let u_2284 : unit = main false 0 0 0 ()
