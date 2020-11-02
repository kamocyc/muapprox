let rec app (_:bool) (_:int) (i:int) (_:bool) (_:int) (h_EXPARAM_112:int)
           (_:bool) (_:int)
           (h:(bool -> int -> int -> bool -> int -> unit -> unit)) (_:bool)
           (_:int) (v:int) (set_flag_f_244:bool) (s_f_x_241:int) (u:unit) : 
  unit =
  if i >= 0
  then
    app
      set_flag_f_244 s_f_x_241 (i - 1) set_flag_f_244 s_f_x_241
      (0 * v + (0 * h_EXPARAM_112 + (0 * i + 0))) set_flag_f_244 s_f_x_241 
      h set_flag_f_244 s_f_x_241 v set_flag_f_244 s_f_x_241 u
  else
    h set_flag_f_244 s_f_x_241 v set_flag_f_244 s_f_x_241 u
let g (_:bool) (_:int) (():unit) : unit = ()
let rec f (prev_set_flag_f_243:bool) (s_prev_f_x_242:int) (x:int) : (
                                                                    bool ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  if prev_set_flag_f_243 then assert false;
  f_without_checking_252 prev_set_flag_f_243 s_prev_f_x_242 x
and f_without_checking_252 (_:bool) (_:int) (x:int) : (bool ->
                                                         int ->
                                                           unit -> unit) =
  let set_flag_f_244 : bool = true
  in
  let s_f_x_241 : int = x
  in
  if x > 0
  then
    app
      set_flag_f_244 s_f_x_241 (Random.int 0) set_flag_f_244 s_f_x_241
      (0 * x + 0) set_flag_f_244 s_f_x_241 f set_flag_f_244 s_f_x_241
      (x - 1)
  else
    g
let main (set_flag_f_244:bool) (s_f_x_241:int) (():unit) : unit =
  f_without_checking_252
    set_flag_f_244 s_f_x_241 (Random.int 0) set_flag_f_244 s_f_x_241 ()
let u_48334 : unit = main false 0 ()
