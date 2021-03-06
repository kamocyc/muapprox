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
      (_:bool) (_:int) (b_EXPARAM_271:int) (set_flag_f5_666:bool)
      (s_f5_e_EXPARAM_660:int) (_:(bool -> int -> unit -> unit)) : (bool ->
                                                                    int ->
                                                                    unit ->
                                                                    unit) =
  a
    set_flag_f5_666 s_f5_e_EXPARAM_660
    (1 * b_EXPARAM_271 + (2 * a_EXPARAM_268 + (-1))) set_flag_f5_666
    s_f5_e_EXPARAM_660 (f1 set_flag_f5_666 s_f5_e_EXPARAM_660 u)
let f3 (_:bool) (_:int) (u:unit) (_:bool) (_:int) (a_EXPARAM_250:int)
      (set_flag_f5_666:bool) (s_f5_e_EXPARAM_660:int)
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
                                                         int -> unit -> unit) =
  a
    set_flag_f5_666 s_f5_e_EXPARAM_660 ((-4) * a_EXPARAM_250 + (-7))
    set_flag_f5_666 s_f5_e_EXPARAM_660
    (f2
      set_flag_f5_666 s_f5_e_EXPARAM_660 u set_flag_f5_666 s_f5_e_EXPARAM_660
      (4 * a_EXPARAM_250 + (-1)) set_flag_f5_666 s_f5_e_EXPARAM_660 a)
let f4 (_:bool) (_:int) (():unit) (_:bool) (_:int) (v:unit) : unit = v
let rec f5 (x_DO_NOT_CARE_683:bool) (x_DO_NOT_CARE_684:int) (u:unit)
          (x_DO_NOT_CARE_681:bool) (x_DO_NOT_CARE_682:int)
          (e_EXPARAM_243:int) (prev_set_flag_f5_665:bool)
          (s_prev_f5_e_EXPARAM_663:int)
          (e:(bool ->
                int ->
                  int ->
                    bool ->
                      int ->
                        (bool -> int -> unit -> unit) ->
                          bool -> int -> unit -> unit)) : (bool ->
                                                             int ->
                                                               unit -> unit) =
  if prev_set_flag_f5_665
  then
    if
      (-3) + -s_prev_f5_e_EXPARAM_663 > (-3) + -e_EXPARAM_243 &&
      (-3) + -e_EXPARAM_243 >= 0
    then
      ()
    else
      assert false;
  f5_without_checking_679
    x_DO_NOT_CARE_683 x_DO_NOT_CARE_684 u x_DO_NOT_CARE_681 x_DO_NOT_CARE_682
    e_EXPARAM_243 prev_set_flag_f5_665 s_prev_f5_e_EXPARAM_663 e
and f5_without_checking_679 (_:bool) (_:int) (u:unit) (_:bool) (_:int)
                           (e_EXPARAM_243:int) (_:bool) (_:int)
                           (e:(bool ->
                                 int ->
                                   int ->
                                     bool ->
                                       int ->
                                         (bool -> int -> unit -> unit) ->
                                           bool -> int -> unit -> unit)) : 
  (bool -> int -> unit -> unit) =
  let set_flag_f5_666 : bool = true
  in
  let s_f5_e_EXPARAM_660 : int = e_EXPARAM_243
  in
  e
    set_flag_f5_666 s_f5_e_EXPARAM_660 (0 * e_EXPARAM_243 + 0)
    set_flag_f5_666 s_f5_e_EXPARAM_660
    (f4 set_flag_f5_666 s_f5_e_EXPARAM_660 u)
let main (set_flag_f5_666:bool) (s_f5_e_EXPARAM_660:int) (u:unit) : unit =
  let zz_1032 : (bool -> int -> unit -> unit) =
    f3
      set_flag_f5_666 s_f5_e_EXPARAM_660 u set_flag_f5_666 s_f5_e_EXPARAM_660
      0 set_flag_f5_666 s_f5_e_EXPARAM_660
      (f5 set_flag_f5_666 s_f5_e_EXPARAM_660 u)
  in
  ()
let u_25188 : unit = main false 0 ()
