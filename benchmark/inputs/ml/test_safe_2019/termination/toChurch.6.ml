let compose (_:bool) (_:int) (_:int) (_:int) (_:bool) (_:int) (_:int)
           (f:(bool -> int -> int -> int -> int)) (_:bool) (_:int) (_:int)
           (_:int) (_:bool) (_:int) (_:int)
           (g:(bool -> int -> int -> int -> int))
           (set_flag_toChurch_354:bool) (s_toChurch_n_347:int)
           (s_toChurch_f_EXPARAM_348:int) (x:int) : int =
  f
    set_flag_toChurch_354 s_toChurch_n_347 s_toChurch_f_EXPARAM_348
    (g set_flag_toChurch_354 s_toChurch_n_347 s_toChurch_f_EXPARAM_348 x)
let id (_:bool) (_:int) (_:int) (x:int) : int = x
let succ (_:bool) (_:int) (_:int) (x:int) : int = x + 1
let rec toChurch (x_DO_NOT_CARE_373:bool) (x_DO_NOT_CARE_374:int)
                (x_DO_NOT_CARE_375:int) (n:int) (x_DO_NOT_CARE_370:bool)
                (x_DO_NOT_CARE_371:int) (x_DO_NOT_CARE_372:int)
                (f_EXPARAM_114:int) (prev_set_flag_toChurch_353:bool)
                (s_prev_toChurch_n_350:int)
                (s_prev_toChurch_f_EXPARAM_351:int)
                (f:(bool -> int -> int -> int -> int)) : (bool ->
                                                            int ->
                                                              int ->
                                                                int -> int) =
  if prev_set_flag_toChurch_353
  then
    if s_prev_toChurch_n_350 > n && n >= 0 then () else assert false;
  toChurch_without_checking_368
    x_DO_NOT_CARE_373 x_DO_NOT_CARE_374 x_DO_NOT_CARE_375 n
    x_DO_NOT_CARE_370 x_DO_NOT_CARE_371 x_DO_NOT_CARE_372
    f_EXPARAM_114 prev_set_flag_toChurch_353 s_prev_toChurch_n_350
    s_prev_toChurch_f_EXPARAM_351 f
and toChurch_without_checking_368 (_:bool) (_:int) (_:int) (n:int)
                                 (_:bool) (_:int) (_:int)
                                 (f_EXPARAM_114:int) (_:bool) (_:int)
                                 (_:int)
                                 (f:(bool -> int -> int -> int -> int)) : 
  (bool -> int -> int -> int -> int) =
  let set_flag_toChurch_354 : bool = true
  in
  let s_toChurch_f_EXPARAM_348 : int = f_EXPARAM_114
  in
  let s_toChurch_n_347 : int = n
  in
  if n = 0
  then
    id
  else
    compose
      set_flag_toChurch_354 s_toChurch_n_347 s_toChurch_f_EXPARAM_348
      (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_toChurch_354
      s_toChurch_n_347 s_toChurch_f_EXPARAM_348 f
      set_flag_toChurch_354 s_toChurch_n_347 s_toChurch_f_EXPARAM_348
      (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_toChurch_354
      s_toChurch_n_347 s_toChurch_f_EXPARAM_348
      (toChurch_without_checking_368
        set_flag_toChurch_354 s_toChurch_n_347
        s_toChurch_f_EXPARAM_348 (n - 1) set_flag_toChurch_354
        s_toChurch_n_347 s_toChurch_f_EXPARAM_348
        (0 * f_EXPARAM_114 + (0 * n + 0)) set_flag_toChurch_354
        s_toChurch_n_347 s_toChurch_f_EXPARAM_348 f)
let main (set_flag_toChurch_354:bool) (s_toChurch_n_347:int)
        (s_toChurch_f_EXPARAM_348:int) (():unit) : unit =
  let x : int = Random.int 0
  in
  (if x >= 0
   then
     let tos : (bool -> int -> int -> int -> int) =
       toChurch
         set_flag_toChurch_354 s_toChurch_n_347
         s_toChurch_f_EXPARAM_348 x set_flag_toChurch_354
         s_toChurch_n_347 s_toChurch_f_EXPARAM_348 0
         set_flag_toChurch_354 s_toChurch_n_347
         s_toChurch_f_EXPARAM_348 succ
     in
     ())
let u_16830 : unit = main false 0 0 ()
