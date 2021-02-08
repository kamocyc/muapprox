let id (_:bool) (_:int) (x:unit) : unit = x
let app (_:bool) (_:int) (_:int) (_:bool) (_:int)
       (h:(bool -> int -> int -> bool -> int -> unit -> unit)) (_:bool)
       (_:int) (v:int) (set_flag_f_182:bool) (s_f_x_179:int) (u:unit) : 
  unit = h set_flag_f_182 s_f_x_179 v set_flag_f_182 s_f_x_179 u
let rec f (prev_set_flag_f_181:bool) (s_prev_f_x_180:int) (x:int) : (
                                                                    bool ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  if prev_set_flag_f_181 then assert false;
  f_without_checking_190 prev_set_flag_f_181 s_prev_f_x_180 x
and f_without_checking_190 (_:bool) (_:int) (x:int) : (bool ->
                                                         int ->
                                                           unit -> unit) =
  let set_flag_f_182 : bool = true
  in
  let s_f_x_179 : int = x
  in
  if x > 0
  then
    app
      set_flag_f_182 s_f_x_179 (0 * x + 0) set_flag_f_182 s_f_x_179
      f_without_checking_190 set_flag_f_182 s_f_x_179 (x - 1)
  else
    id
let main (set_flag_f_182:bool) (s_f_x_179:int) (():unit) : unit =
  f set_flag_f_182 s_f_x_179 (Random.int 0) set_flag_f_182 s_f_x_179 ()
let u_8826 : unit = main false 0 ()
