let rec app (_:bool) (i:int) (_:bool) (h_EXPARAM_112:int) (_:bool)
           (h:(bool -> int -> bool -> unit -> unit)) (_:bool) (v:int)
           (set_flag_g_199:bool) (u:unit) : unit =
  if i >= 0
  then
    app
      set_flag_g_199 (i - 1) set_flag_g_199
      (0 * v + (0 * h_EXPARAM_112 + (0 * i + 0))) set_flag_g_199 h
      set_flag_g_199 v set_flag_g_199 u
  else
    h set_flag_g_199 v set_flag_g_199 u
let rec g (prev_set_flag_g_198:bool) (u:unit) : unit =
  if prev_set_flag_g_198 then assert false;
  g_without_checking_213 prev_set_flag_g_198 u
and g_without_checking_213 (_:bool) (():unit) : unit =
  let set_flag_g_199 : bool = true
  in
  ()
let rec f (set_flag_g_199:bool) (x:int) : (bool -> unit -> unit) =
  if x > 0
  then
    app
      set_flag_g_199 (Random.int 0) set_flag_g_199 (0 * x + 0)
      set_flag_g_199 f set_flag_g_199 (x - 1)
  else
    g
let main (set_flag_g_199:bool) (():unit) : unit =
  f set_flag_g_199 (Random.int 0) set_flag_g_199 ()
let u_42240 : unit = main false ()
