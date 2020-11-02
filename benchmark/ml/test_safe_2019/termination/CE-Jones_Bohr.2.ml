let f1 (_:bool) (_:int) (_:int) (():unit) (_:bool) (_:int) (_:int) (_:int)
      (_:bool) (_:int) (_:int) (_:(bool -> int -> int -> unit -> unit))
      (_:bool) (_:int) (_:int) (d:unit) : unit = d
let rec f2 (x_DO_NOT_CARE_447:bool) (x_DO_NOT_CARE_448:int)
          (x_DO_NOT_CARE_449:int) (u:unit) (x_DO_NOT_CARE_444:bool)
          (x_DO_NOT_CARE_445:int) (x_DO_NOT_CARE_446:int) (a_EXPARAM_268:int)
          (x_DO_NOT_CARE_441:bool) (x_DO_NOT_CARE_442:int)
          (x_DO_NOT_CARE_443:int)
          (a:(bool ->
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
                                              int -> int -> unit -> unit) ->
                                             bool ->
                                               int -> int -> unit -> unit) ->
                              bool -> int -> int -> unit -> unit))
          (x_DO_NOT_CARE_438:bool) (x_DO_NOT_CARE_439:int)
          (x_DO_NOT_CARE_440:int) (b_EXPARAM_271:int)
          (prev_set_flag_f2_390:bool) (s_prev_f2_a_EXPARAM_386:int)
          (s_prev_f2_b_EXPARAM_388:int)
          (b:(bool -> int -> int -> unit -> unit)) : (bool ->
                                                        int ->
                                                          int -> unit -> unit) =
  if prev_set_flag_f2_390 then assert false;
  f2_without_checking_436
    x_DO_NOT_CARE_447 x_DO_NOT_CARE_448 x_DO_NOT_CARE_449 u
    x_DO_NOT_CARE_444 x_DO_NOT_CARE_445 x_DO_NOT_CARE_446 a_EXPARAM_268
    x_DO_NOT_CARE_441 x_DO_NOT_CARE_442 x_DO_NOT_CARE_443 a
    x_DO_NOT_CARE_438 x_DO_NOT_CARE_439 x_DO_NOT_CARE_440 b_EXPARAM_271
    prev_set_flag_f2_390 s_prev_f2_a_EXPARAM_386 s_prev_f2_b_EXPARAM_388
    b
and f2_without_checking_436 (_:bool) (_:int) (_:int) (u:unit) (_:bool)
                           (_:int) (_:int) (a_EXPARAM_268:int) (_:bool)
                           (_:int) (_:int)
                           (a:(bool ->
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
                                                                   unit ->
                                                                    unit) ->
                                                              bool ->
                                                                int ->
                                                                  int ->
                                                                    unit ->
                                                                    unit) ->
                                               bool ->
                                                 int ->
                                                   int -> unit -> unit))
                           (_:bool) (_:int) (_:int) (b_EXPARAM_271:int)
                           (_:bool) (_:int) (_:int)
                           (_:(bool -> int -> int -> unit -> unit)) : 
  (bool -> int -> int -> unit -> unit) =
  let set_flag_f2_391 : bool = true
  in
  let s_f2_b_EXPARAM_383 : int = b_EXPARAM_271
  in
  let s_f2_a_EXPARAM_381 : int = a_EXPARAM_268
  in
  a
    set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
    (0 * b_EXPARAM_271 + (0 * a_EXPARAM_268 + 0)) set_flag_f2_391
    s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
    (f1 set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 u)
let f3 (_:bool) (_:int) (_:int) (u:unit) (_:bool) (_:int) (_:int)
      (a_EXPARAM_250:int) (set_flag_f2_391:bool) (s_f2_a_EXPARAM_381:int)
      (s_f2_b_EXPARAM_383:int)
      (a:(bool ->
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
                                          int -> int -> unit -> unit) ->
                                         bool ->
                                           int -> int -> unit -> unit) ->
                          bool -> int -> int -> unit -> unit)) : (bool ->
                                                                    int ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  a
    set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
    (0 * a_EXPARAM_250 + 0) set_flag_f2_391 s_f2_a_EXPARAM_381
    s_f2_b_EXPARAM_383
    (f2
      set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 u
      set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
      (0 * a_EXPARAM_250 + 0) set_flag_f2_391 s_f2_a_EXPARAM_381
      s_f2_b_EXPARAM_383 a)
let f4 (_:bool) (_:int) (_:int) (():unit) (_:bool) (_:int) (_:int)
      (v:unit) : unit = v
let f5 (_:bool) (_:int) (_:int) (u:unit) (_:bool) (_:int) (_:int)
      (e_EXPARAM_243:int) (set_flag_f2_391:bool) (s_f2_a_EXPARAM_381:int)
      (s_f2_b_EXPARAM_383:int)
      (e:(bool ->
            int ->
              int ->
                int ->
                  bool ->
                    int ->
                      int ->
                        (bool -> int -> int -> unit -> unit) ->
                          bool -> int -> int -> unit -> unit)) : (bool ->
                                                                    int ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  e
    set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
    (0 * e_EXPARAM_243 + 0) set_flag_f2_391 s_f2_a_EXPARAM_381
    s_f2_b_EXPARAM_383
    (f4 set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 u)
let main (set_flag_f2_391:bool) (s_f2_a_EXPARAM_381:int)
        (s_f2_b_EXPARAM_383:int) (u:unit) : unit =
  let zz_1032 : (bool -> int -> int -> unit -> unit) =
    f3
      set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 u
      set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 0
      set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383
      (f5 set_flag_f2_391 s_f2_a_EXPARAM_381 s_f2_b_EXPARAM_383 u)
  in
  ()
let u_8541 : unit = main false 0 0 ()
