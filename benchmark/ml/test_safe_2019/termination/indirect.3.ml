let id (_:bool) (_:int) (_:int) (x:unit) : unit = x
let rec app (x_DO_NOT_CARE_156:bool) (x_DO_NOT_CARE_157:int)
           (x_DO_NOT_CARE_158:int) (h_EXPARAM_78:int)
           (x_DO_NOT_CARE_153:bool) (x_DO_NOT_CARE_154:int)
           (x_DO_NOT_CARE_155:int)
           (h:(bool ->
                 int -> int -> int -> bool -> int -> int -> unit -> unit))
           (x_DO_NOT_CARE_150:bool) (x_DO_NOT_CARE_151:int)
           (x_DO_NOT_CARE_152:int) (v:int) (prev_set_flag_app_127:bool)
           (s_prev_app_h_EXPARAM_123:int) (s_prev_app_v_125:int) (u:unit) : 
  unit =
  if prev_set_flag_app_127
  then
    if s_prev_app_v_125 > v && v >= 0 then () else assert false;
  app_without_checking_148
    x_DO_NOT_CARE_156 x_DO_NOT_CARE_157 x_DO_NOT_CARE_158
    h_EXPARAM_78 x_DO_NOT_CARE_153 x_DO_NOT_CARE_154
    x_DO_NOT_CARE_155 h x_DO_NOT_CARE_150 x_DO_NOT_CARE_151
    x_DO_NOT_CARE_152 v prev_set_flag_app_127
    s_prev_app_h_EXPARAM_123 s_prev_app_v_125 u
and app_without_checking_148 (_:bool) (_:int) (_:int)
                            (h_EXPARAM_78:int) (_:bool) (_:int)
                            (_:int)
                            (h:(bool ->
                                  int ->
                                    int ->
                                      int ->
                                        bool ->
                                          int -> int -> unit -> unit))
                            (_:bool) (_:int) (_:int) (v:int) (_:bool)
                            (_:int) (_:int) (u:unit) : unit =
  let set_flag_app_128 : bool = true
  in
  let s_app_v_121 : int = v
  in
  let s_app_h_EXPARAM_119 : int = h_EXPARAM_78
  in
  h
    set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 v
    set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 u
let rec f (set_flag_app_128:bool) (s_app_h_EXPARAM_119:int)
         (s_app_v_121:int) (x:int) : (bool ->
                                        int -> int -> unit -> unit) =
  if x > 0
  then
    app
      set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 (0 * x + 0)
      set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 f
      set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 (x - 1)
  else
    id
let main (set_flag_app_128:bool) (s_app_h_EXPARAM_119:int)
        (s_app_v_121:int) (():unit) : unit =
  f
    set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 (Random.int 0)
    set_flag_app_128 s_app_h_EXPARAM_119 s_app_v_121 ()
let u_5362 : unit = main false 0 0 ()
