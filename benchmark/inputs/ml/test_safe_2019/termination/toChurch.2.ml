let compose (_:bool) (_:int) (_:int) (_:bool) (_:int)
           (f:(bool -> int -> int -> int)) (_:bool) (_:int) (_:int) (_:bool)
           (_:int) (g:(bool -> int -> int -> int)) (set_flag_id_228:bool)
           (s_id_x_225:int) (x:int) : int =
  f set_flag_id_228 s_id_x_225 (g set_flag_id_228 s_id_x_225 x)
let rec id (prev_set_flag_id_227:bool) (s_prev_id_x_226:int) (x:int) : 
  int =
  if prev_set_flag_id_227 then assert false;
  id_without_checking_254 prev_set_flag_id_227 s_prev_id_x_226 x
and id_without_checking_254 (_:bool) (_:int) (x:int) : int =
  let set_flag_id_228 : bool = true
  in
  let s_id_x_225 : int = x
  in
  x
let succ (_:bool) (_:int) (x:int) : int = x + 1
let rec toChurch (_:bool) (_:int) (n:int) (_:bool) (_:int)
                (f_EXPARAM_114:int) (set_flag_id_228:bool)
                (s_id_x_225:int) (f:(bool -> int -> int -> int)) : (bool ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  if n = 0
  then
    id
  else
    compose
      set_flag_id_228 s_id_x_225 (0 * f_EXPARAM_114 + (0 * n + 0))
      set_flag_id_228 s_id_x_225 f set_flag_id_228 s_id_x_225
      (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_id_228 s_id_x_225
      (toChurch
        set_flag_id_228 s_id_x_225 (n - 1) set_flag_id_228 s_id_x_225
        (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_id_228 s_id_x_225 
        f)
let main (set_flag_id_228:bool) (s_id_x_225:int) (():unit) : unit =
  let x : int = Random.int 0
  in
  (if x >= 0
   then
     let tos : (bool -> int -> int -> int) =
       toChurch
         set_flag_id_228 s_id_x_225 x set_flag_id_228 s_id_x_225 0
         set_flag_id_228 s_id_x_225 succ
     in
     ())
let u_5600 : unit = main false 0 ()
