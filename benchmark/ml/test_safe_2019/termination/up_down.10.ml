let rec app (x_DO_NOT_CARE_187:bool) (x_DO_NOT_CARE_188:int)
           (x_DO_NOT_CARE_189:int) (f_EXPARAM_81:int)
           (x_DO_NOT_CARE_184:bool) (x_DO_NOT_CARE_185:int)
           (x_DO_NOT_CARE_186:int) (f:(bool -> int -> int -> int -> unit))
           (prev_set_flag_app_167:bool) (s_prev_app_f_EXPARAM_164:int)
           (s_prev_app_x_166:int) (x:int) : unit =
  if prev_set_flag_app_167 then assert false;
  app_without_checking_182
    x_DO_NOT_CARE_187 x_DO_NOT_CARE_188 x_DO_NOT_CARE_189 f_EXPARAM_81
    x_DO_NOT_CARE_184 x_DO_NOT_CARE_185 x_DO_NOT_CARE_186 f
    prev_set_flag_app_167 s_prev_app_f_EXPARAM_164 s_prev_app_x_166 x
and app_without_checking_182 (_:bool) (_:int) (_:int) (f_EXPARAM_81:int)
                            (_:bool) (_:int) (_:int)
                            (f:(bool -> int -> int -> int -> unit))
                            (_:bool) (_:int) (_:int) (x:int) : unit =
  let set_flag_app_168 : bool = true
  in
  let s_app_x_163 : int = x
  in
  let s_app_f_EXPARAM_161 : int = f_EXPARAM_81
  in
  f set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 x
and down (set_flag_app_168:bool) (s_app_f_EXPARAM_161:int)
        (s_app_x_163:int) (x:int) : unit =
  if x = 0
  then
    ()
  else
    down set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 (x - 1)
and up (set_flag_app_168:bool) (s_app_f_EXPARAM_161:int)
      (s_app_x_163:int) (x:int) : unit =
  if x = 0
  then
    ()
  else
    up set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 (x + 1)
let main (set_flag_app_168:bool) (s_app_f_EXPARAM_161:int)
        (s_app_x_163:int) (():unit) : unit =
  let t1 : int = Random.int 0
  in
  let t2 : int = Random.int 0
  in
  if t1 > 0
  then
    app
      set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 0 set_flag_app_168
      s_app_f_EXPARAM_161 s_app_x_163 down set_flag_app_168
      s_app_f_EXPARAM_161 s_app_x_163 t1
  else
    (if t2 < 0
     then
       app_without_checking_182
         set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 0
         set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 up
         set_flag_app_168 s_app_f_EXPARAM_161 s_app_x_163 t2)
let u_15212 : unit = main false 0 0 ()
