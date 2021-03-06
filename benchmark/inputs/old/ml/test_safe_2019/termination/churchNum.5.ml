let succ (_:bool) (_:int) (_:int) (m_EXPARAM_238:int) (_:bool) (_:int)
        (_:int)
        (m:(bool ->
              int ->
                int ->
                  int ->
                    bool ->
                      int ->
                        int ->
                          (bool -> int -> int -> int -> int) ->
                            bool -> int -> int -> int -> int))
        (_:bool) (_:int) (_:int) (s_EXPARAM_240:int) (_:bool) (_:int) 
        (_:int) (s:(bool -> int -> int -> int -> int))
        (set_flag_zero_513:bool) (s_zero_f_EXPARAM_506:int)
        (s_zero_z_508:int) (z:int) : int =
  m
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508
    (0 * z + (0 * s_EXPARAM_240 + (0 * m_EXPARAM_238 + 0))) set_flag_zero_513
    s_zero_f_EXPARAM_506 s_zero_z_508 s set_flag_zero_513
    s_zero_f_EXPARAM_506 s_zero_z_508
    (s set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 z)
let id (_:bool) (_:int) (_:int) (x:int) : int = x
let two (_:bool) (_:int) (_:int) (f_EXPARAM_212:int) (_:bool) (_:int) 
       (_:int)
       (f:(bool ->
             int ->
               int ->
                 int ->
                   bool ->
                     int ->
                       int ->
                         (bool ->
                            int ->
                              int ->
                                int ->
                                  bool ->
                                    int ->
                                      int ->
                                        (bool -> int -> int -> int -> int) ->
                                          bool -> int -> int -> int -> int) ->
                           bool ->
                             int ->
                               int ->
                                 int ->
                                   bool ->
                                     int ->
                                       int ->
                                         (bool -> int -> int -> int -> int) ->
                                           bool -> int -> int -> int -> int))
       (_:bool) (_:int) (_:int) (z_EXPARAM_216:int) (set_flag_zero_513:bool)
       (s_zero_f_EXPARAM_506:int) (s_zero_z_508:int)
       (z:(bool ->
             int ->
               int ->
                 int ->
                   bool ->
                     int ->
                       int ->
                         (bool -> int -> int -> int -> int) ->
                           bool -> int -> int -> int -> int)) : (bool ->
                                                                   int ->
                                                                    int ->
                                                                    int ->
                                                                    bool ->
                                                                    int ->
                                                                    int ->
                                                                    (bool ->
                                                                    int ->
                                                                    int ->
                                                                    int ->
                                                                    int) ->
                                                                    bool ->
                                                                    int ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  f
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508
    (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_zero_513
    s_zero_f_EXPARAM_506 s_zero_z_508
    (f
      set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508
      (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_zero_513
      s_zero_f_EXPARAM_506 s_zero_z_508 z)
let rec zero (x_DO_NOT_CARE_530:bool) (x_DO_NOT_CARE_531:int)
            (x_DO_NOT_CARE_532:int) (f_EXPARAM_210:int)
            (x_DO_NOT_CARE_527:bool) (x_DO_NOT_CARE_528:int)
            (x_DO_NOT_CARE_529:int) (f:(bool -> int -> int -> int -> int))
            (prev_set_flag_zero_512:bool) (s_prev_zero_f_EXPARAM_509:int)
            (s_prev_zero_z_511:int) (z:int) : int =
  if prev_set_flag_zero_512 then assert false;
  zero_without_checking_525
    x_DO_NOT_CARE_530 x_DO_NOT_CARE_531 x_DO_NOT_CARE_532 f_EXPARAM_210
    x_DO_NOT_CARE_527 x_DO_NOT_CARE_528 x_DO_NOT_CARE_529 f
    prev_set_flag_zero_512 s_prev_zero_f_EXPARAM_509 s_prev_zero_z_511 
    z
and zero_without_checking_525 (_:bool) (_:int) (_:int)
                             (f_EXPARAM_210:int) (_:bool) (_:int) (_:int)
                             (_:(bool -> int -> int -> int -> int))
                             (_:bool) (_:int) (_:int) (z:int) : int =
  let set_flag_zero_513 : bool = true
  in
  let s_zero_z_508 : int = z
  in
  let s_zero_f_EXPARAM_506 : int = f_EXPARAM_210
  in
  z
let main (set_flag_zero_513:bool) (s_zero_f_EXPARAM_506:int)
        (s_zero_z_508:int) (():unit) : int =
  two
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 0
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 succ
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 0
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 zero
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 0
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 id
    set_flag_zero_513 s_zero_f_EXPARAM_506 s_zero_z_508 0
let u_30412 : int = main false 0 0 ()
