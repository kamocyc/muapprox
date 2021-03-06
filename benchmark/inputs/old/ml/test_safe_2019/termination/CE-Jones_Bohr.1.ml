let rec f1 (x_DO_NOT_CARE_356:bool) (x_DO_NOT_CARE_357:int) (u:unit)
          (x_DO_NOT_CARE_354:bool) (x_DO_NOT_CARE_355:int)
          (c_EXPARAM_282:int) (x_DO_NOT_CARE_352:bool)
          (x_DO_NOT_CARE_353:int) (c:(bool -> int -> unit -> unit))
          (prev_set_flag_f1_292:bool) (s_prev_f1_c_EXPARAM_289:int) (
          d:unit) : unit =
  if prev_set_flag_f1_292 then assert false;
  f1_without_checking_350
    x_DO_NOT_CARE_356 x_DO_NOT_CARE_357 u x_DO_NOT_CARE_354
    x_DO_NOT_CARE_355 c_EXPARAM_282 x_DO_NOT_CARE_352 x_DO_NOT_CARE_353 
    c prev_set_flag_f1_292 s_prev_f1_c_EXPARAM_289 d
and f1_without_checking_350 (_:bool) (_:int) (():unit) (_:bool) (_:int)
                           (c_EXPARAM_282:int) (_:bool) (_:int)
                           (_:(bool -> int -> unit -> unit)) (_:bool)
                           (_:int) (d:unit) : unit =
  let set_flag_f1_293 : bool = true
  in
  let s_f1_c_EXPARAM_285 : int = c_EXPARAM_282
  in
  d
let f2 (_:bool) (_:int) (u:unit) (_:bool) (_:int) (a_EXPARAM_268:int)
      (_:bool) (_:int)
      (a:(bool ->
            int ->
              int ->
                bool ->
                  int ->
                    (bool ->
                       int ->
                         int ->
                           bool ->
                             int ->
                               (bool -> int -> unit -> unit) ->
                                 bool -> int -> unit -> unit) ->
                      bool -> int -> unit -> unit))
      (_:bool) (_:int) (b_EXPARAM_271:int) (set_flag_f1_293:bool)
      (s_f1_c_EXPARAM_285:int) (_:(bool -> int -> unit -> unit)) : (bool ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  a
    set_flag_f1_293 s_f1_c_EXPARAM_285
    (0 * b_EXPARAM_271 + (0 * a_EXPARAM_268 + 0)) set_flag_f1_293
    s_f1_c_EXPARAM_285 (f1 set_flag_f1_293 s_f1_c_EXPARAM_285 u)
let f3 (_:bool) (_:int) (u:unit) (_:bool) (_:int) (a_EXPARAM_250:int)
      (set_flag_f1_293:bool) (s_f1_c_EXPARAM_285:int)
      (a:(bool ->
            int ->
              int ->
                bool ->
                  int ->
                    (bool ->
                       int ->
                         int ->
                           bool ->
                             int ->
                               (bool -> int -> unit -> unit) ->
                                 bool -> int -> unit -> unit) ->
                      bool -> int -> unit -> unit)) : (bool ->
                                                         int ->
                                                           unit -> unit) =
  a
    set_flag_f1_293 s_f1_c_EXPARAM_285 (0 * a_EXPARAM_250 + 0)
    set_flag_f1_293 s_f1_c_EXPARAM_285
    (f2
      set_flag_f1_293 s_f1_c_EXPARAM_285 u set_flag_f1_293
      s_f1_c_EXPARAM_285 (0 * a_EXPARAM_250 + 0) set_flag_f1_293
      s_f1_c_EXPARAM_285 a)
let f4 (_:bool) (_:int) (():unit) (_:bool) (_:int) (v:unit) : unit = v
let f5 (_:bool) (_:int) (u:unit) (_:bool) (_:int) (e_EXPARAM_243:int)
      (set_flag_f1_293:bool) (s_f1_c_EXPARAM_285:int)
      (e:(bool ->
            int ->
              int ->
                bool ->
                  int ->
                    (bool -> int -> unit -> unit) ->
                      bool -> int -> unit -> unit)) : (bool ->
                                                         int ->
                                                           unit -> unit) =
  e
    set_flag_f1_293 s_f1_c_EXPARAM_285 (0 * e_EXPARAM_243 + 0)
    set_flag_f1_293 s_f1_c_EXPARAM_285
    (f4 set_flag_f1_293 s_f1_c_EXPARAM_285 u)
let main (set_flag_f1_293:bool) (s_f1_c_EXPARAM_285:int) (u:unit) : unit =
  let zz_1032 : (bool -> int -> unit -> unit) =
    f3
      set_flag_f1_293 s_f1_c_EXPARAM_285 u set_flag_f1_293
      s_f1_c_EXPARAM_285 0 set_flag_f1_293 s_f1_c_EXPARAM_285
      (f5 set_flag_f1_293 s_f1_c_EXPARAM_285 u)
  in
  ()
let u_2635 : unit = main false 0 ()
