let f1 (_:bool) (_:int) (():unit) (_:bool) (_:int) (_:int) (_:bool) (_:int)
      (_:(bool -> int -> unit -> unit)) (_:bool) (_:int) (d:unit) : unit = 
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
      (_:bool) (_:int) (b_EXPARAM_271:int) (set_flag_f3_493:bool)
      (s_f3_a_EXPARAM_487:int) (_:(bool -> int -> unit -> unit)) : (bool ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  a
    set_flag_f3_493 s_f3_a_EXPARAM_487
    (0 * b_EXPARAM_271 + (0 * a_EXPARAM_268 + 0)) set_flag_f3_493
    s_f3_a_EXPARAM_487 (f1 set_flag_f3_493 s_f3_a_EXPARAM_487 u)
let rec f3 (x_DO_NOT_CARE_528:bool) (x_DO_NOT_CARE_529:int) (u:unit)
          (x_DO_NOT_CARE_526:bool) (x_DO_NOT_CARE_527:int)
          (a_EXPARAM_250:int) (prev_set_flag_f3_492:bool)
          (s_prev_f3_a_EXPARAM_490:int)
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
  if prev_set_flag_f3_492 then assert false;
  f3_without_checking_524
    x_DO_NOT_CARE_528 x_DO_NOT_CARE_529 u x_DO_NOT_CARE_526
    x_DO_NOT_CARE_527 a_EXPARAM_250 prev_set_flag_f3_492
    s_prev_f3_a_EXPARAM_490 a
and f3_without_checking_524 (_:bool) (_:int) (u:unit) (_:bool) (_:int)
                           (a_EXPARAM_250:int) (_:bool) (_:int)
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
                                                    (bool ->
                                                       int ->
                                                         unit -> unit) ->
                                                      bool ->
                                                        int ->
                                                          unit -> unit) ->
                                           bool -> int -> unit -> unit)) : 
  (bool -> int -> unit -> unit) =
  let set_flag_f3_493 : bool = true
  in
  let s_f3_a_EXPARAM_487 : int = a_EXPARAM_250
  in
  a
    set_flag_f3_493 s_f3_a_EXPARAM_487 (0 * a_EXPARAM_250 + 0)
    set_flag_f3_493 s_f3_a_EXPARAM_487
    (f2
      set_flag_f3_493 s_f3_a_EXPARAM_487 u set_flag_f3_493
      s_f3_a_EXPARAM_487 (0 * a_EXPARAM_250 + 0) set_flag_f3_493
      s_f3_a_EXPARAM_487 a)
let f4 (_:bool) (_:int) (():unit) (_:bool) (_:int) (v:unit) : unit = v
let f5 (_:bool) (_:int) (u:unit) (_:bool) (_:int) (e_EXPARAM_243:int)
      (set_flag_f3_493:bool) (s_f3_a_EXPARAM_487:int)
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
    set_flag_f3_493 s_f3_a_EXPARAM_487 (0 * e_EXPARAM_243 + 0)
    set_flag_f3_493 s_f3_a_EXPARAM_487
    (f4 set_flag_f3_493 s_f3_a_EXPARAM_487 u)
let main (set_flag_f3_493:bool) (s_f3_a_EXPARAM_487:int) (u:unit) : unit =
  let zz_1032 : (bool -> int -> unit -> unit) =
    f3
      set_flag_f3_493 s_f3_a_EXPARAM_487 u set_flag_f3_493
      s_f3_a_EXPARAM_487 0 set_flag_f3_493 s_f3_a_EXPARAM_487
      (f5 set_flag_f3_493 s_f3_a_EXPARAM_487 u)
  in
  ()
let u_13849 : unit = main false 0 ()
