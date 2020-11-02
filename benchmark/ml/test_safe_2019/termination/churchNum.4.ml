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
        (set_flag_two_426:bool) (s_two_f_EXPARAM_417:int)
        (s_two_z_EXPARAM_419:int) (z:int) : int =
  m
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419
    (0 * z + (0 * s_EXPARAM_240 + (0 * m_EXPARAM_238 + 0))) set_flag_two_426
    s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 s set_flag_two_426
    s_two_f_EXPARAM_417 s_two_z_EXPARAM_419
    (s set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 z)
let id (_:bool) (_:int) (_:int) (x:int) : int = x
let rec two (x_DO_NOT_CARE_458:bool) (x_DO_NOT_CARE_459:int)
           (x_DO_NOT_CARE_460:int) (f_EXPARAM_212:int)
           (x_DO_NOT_CARE_455:bool) (x_DO_NOT_CARE_456:int)
           (x_DO_NOT_CARE_457:int)
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
                                              bool ->
                                                int -> int -> int -> int) ->
                               bool ->
                                 int ->
                                   int ->
                                     int ->
                                       bool ->
                                         int ->
                                           int ->
                                             (bool ->
                                                int -> int -> int -> int) ->
                                               bool ->
                                                 int -> int -> int -> int))
           (x_DO_NOT_CARE_452:bool) (x_DO_NOT_CARE_453:int)
           (x_DO_NOT_CARE_454:int) (z_EXPARAM_216:int)
           (prev_set_flag_two_425:bool) (s_prev_two_f_EXPARAM_421:int)
           (s_prev_two_z_EXPARAM_423:int)
           (z:(bool ->
                 int ->
                   int ->
                     int ->
                       bool ->
                         int ->
                           int ->
                             (bool -> int -> int -> int -> int) ->
                               bool -> int -> int -> int -> int)) : (
                                                                    bool ->
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
  if prev_set_flag_two_425 then assert false;
  two_without_checking_450
    x_DO_NOT_CARE_458 x_DO_NOT_CARE_459 x_DO_NOT_CARE_460 f_EXPARAM_212
    x_DO_NOT_CARE_455 x_DO_NOT_CARE_456 x_DO_NOT_CARE_457 f
    x_DO_NOT_CARE_452 x_DO_NOT_CARE_453 x_DO_NOT_CARE_454 z_EXPARAM_216
    prev_set_flag_two_425 s_prev_two_f_EXPARAM_421
    s_prev_two_z_EXPARAM_423 z
and two_without_checking_450 (_:bool) (_:int) (_:int) (f_EXPARAM_212:int)
                            (_:bool) (_:int) (_:int)
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
                                                             (bool ->
                                                                int ->
                                                                  int ->
                                                                    int ->
                                                                    int) ->
                                                               bool ->
                                                                 int ->
                                                                   int ->
                                                                    int ->
                                                                    int) ->
                                                bool ->
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
                                                                    int))
                            (_:bool) (_:int) (_:int) (z_EXPARAM_216:int)
                            (_:bool) (_:int) (_:int)
                            (z:(bool ->
                                  int ->
                                    int ->
                                      int ->
                                        bool ->
                                          int ->
                                            int ->
                                              (bool ->
                                                 int -> int -> int -> int) ->
                                                bool ->
                                                  int ->
                                                    int -> int -> int)) : 
  (bool ->
     int ->
       int ->
         int ->
           bool ->
             int ->
               int ->
                 (bool -> int -> int -> int -> int) ->
                   bool -> int -> int -> int -> int) =
  let set_flag_two_426 : bool = true
  in
  let s_two_z_EXPARAM_419 : int = z_EXPARAM_216
  in
  let s_two_f_EXPARAM_417 : int = f_EXPARAM_212
  in
  f
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419
    (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_two_426
    s_two_f_EXPARAM_417 s_two_z_EXPARAM_419
    (f
      set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419
      (0 * z_EXPARAM_216 + (0 * f_EXPARAM_212 + 0)) set_flag_two_426
      s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 z)
let zero (_:bool) (_:int) (_:int) (_:int) (_:bool) (_:int) (_:int)
        (_:(bool -> int -> int -> int -> int)) (_:bool) (_:int) (_:int)
        (z:int) : int = z
let main (set_flag_two_426:bool) (s_two_f_EXPARAM_417:int)
        (s_two_z_EXPARAM_419:int) (():unit) : int =
  two
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 0
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 succ
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 0
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 zero
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 0
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 id
    set_flag_two_426 s_two_f_EXPARAM_417 s_two_z_EXPARAM_419 0
let u_24386 : int = main false 0 0 ()
