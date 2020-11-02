let f1 (_:bool) (():unit) (_:bool) (_:int) (_:bool)
      (_:(bool -> unit -> unit)) (_:bool) (d:unit) : unit = d
let f2 (_:bool) (u:unit) (_:bool) (a_EXPARAM_268:int) (_:bool)
      (a:(bool ->
            int ->
              bool ->
                (bool ->
                   int ->
                     bool -> (bool -> unit -> unit) -> bool -> unit -> unit) ->
                  bool -> unit -> unit))
      (_:bool) (b_EXPARAM_271:int) (set_flag_f4_581:bool)
      (_:(bool -> unit -> unit)) : (bool -> unit -> unit) =
  a
    set_flag_f4_581 (0 * b_EXPARAM_271 + (0 * a_EXPARAM_268 + 0))
    set_flag_f4_581 (f1 set_flag_f4_581 u)
let f3 (_:bool) (u:unit) (_:bool) (a_EXPARAM_250:int) (set_flag_f4_581:bool)
      (a:(bool ->
            int ->
              bool ->
                (bool ->
                   int ->
                     bool -> (bool -> unit -> unit) -> bool -> unit -> unit) ->
                  bool -> unit -> unit)) : (bool -> unit -> unit) =
  a
    set_flag_f4_581 (0 * a_EXPARAM_250 + 0) set_flag_f4_581
    (f2
      set_flag_f4_581 u set_flag_f4_581 (0 * a_EXPARAM_250 + 0)
      set_flag_f4_581 a)
let rec f4 (x_DO_NOT_CARE_604:bool) (u:unit) (prev_set_flag_f4_580:bool)
          (v:unit) : unit =
  if prev_set_flag_f4_580 then assert false;
  f4_without_checking_602 x_DO_NOT_CARE_604 u prev_set_flag_f4_580 v
and f4_without_checking_602 (_:bool) (():unit) (_:bool) (v:unit) : unit =
  let set_flag_f4_581 : bool = true
  in
  v
let f5 (_:bool) (u:unit) (_:bool) (e_EXPARAM_243:int)
      (set_flag_f4_581:bool)
      (e:(bool ->
            int -> bool -> (bool -> unit -> unit) -> bool -> unit -> unit)) : 
  (bool -> unit -> unit) =
  e
    set_flag_f4_581 (0 * e_EXPARAM_243 + 0) set_flag_f4_581
    (f4 set_flag_f4_581 u)
let main (set_flag_f4_581:bool) (u:unit) : unit =
  let zz_1032 : (bool -> unit -> unit) =
    f3
      set_flag_f4_581 u set_flag_f4_581 0 set_flag_f4_581
      (f5 set_flag_f4_581 u)
  in
  ()
let u_17266 : unit = main false ()
