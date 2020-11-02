let succ (_:bool) (_:int) (m_EXPARAM_238:int) (_:bool) (_:int)
        (m:(bool ->
              int ->
                int ->
                  bool ->
                    int ->
                      (bool -> int -> int -> int) ->
                        bool -> int -> int -> int))
        (_:bool) (_:int) (s_EXPARAM_240:int) (_:bool) (_:int)
        (s:(bool -> int -> int -> int)) (set_flag_id_352:bool)
        (s_id_x_349:int) (z:int) : int =
  m
    set_flag_id_352 s_id_x_349
    (0 * z + (0 * s_EXPARAM_240 + (0 * m_EXPARAM_238 + 0))) set_flag_id_352
    s_id_x_349 s set_flag_id_352 s_id_x_349 (s set_flag_id_352 s_id_x_349 z)
let rec id (prev_set_flag_id_351:bool) (s_prev_id_x_350:int) (x:int) : 
  int =
  if prev_set_flag_id_351 then assert false;
  id_without_checking_382 prev_set_flag_id_351 s_prev_id_x_350 x
and id_without_checking_382 (_:bool) (_:int) (x:int) : int =
  let set_flag_id_352 : bool = true
  in
  let s_id_x_349 : int = x
  in
  x
let two (_:bool) (_:int) (f_EXPARAM_212:int) (_:bool) (_:int)
       (f:(bool ->
             int ->
               int ->
                 bool ->
                   int ->
                     (bool ->
                        int ->
                          int ->
                            bool ->
                              int ->
                                (bool -> int -> int -> int) ->
                                  bool -> int -> int -> int) ->
                       bool ->
                         int ->
                           int ->
                             bool ->
                               int ->
                                 (bool -> int -> int -> int) ->
                                   bool -> int -> int -> int))
       (_:bool) (_:int) (z_EXPARAM_216:int) (set_flag_id_352:bool)
       (s_id_x_349:int)
       (z:(bool ->
             int ->
               int ->
                 bool ->
                   int ->
                     (bool -> int -> int -> int) ->
                       bool -> int -> int -> int)) : (bool ->
                                                        int ->
                                                          int ->
                                                            bool ->
                                                              int ->
                                                                (bool ->
                                                                   int ->
                                                                    int ->
                                                                    int) ->
                                                                  bool ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  f
    set_flag_id_352 s_id_x_349
    (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_id_352
    s_id_x_349
    (f
      set_flag_id_352 s_id_x_349
      (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_id_352
      s_id_x_349 z)
let zero (_:bool) (_:int) (_:int) (_:bool) (_:int)
        (_:(bool -> int -> int -> int)) (_:bool) (_:int) (z:int) : int =
  z
let main (set_flag_id_352:bool) (s_id_x_349:int) (():unit) : int =
  two
    set_flag_id_352 s_id_x_349 0 set_flag_id_352 s_id_x_349 succ
    set_flag_id_352 s_id_x_349 0 set_flag_id_352 s_id_x_349 zero
    set_flag_id_352 s_id_x_349 0 set_flag_id_352 s_id_x_349 id
    set_flag_id_352 s_id_x_349 0
let u_18512 : int = main false 0 ()
