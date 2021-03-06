let rec map (_:bool) (_:int) (_:int) (f_EXPARAM_121:int) (_:bool) (_:int)
           (_:int) (f:(bool -> int -> int -> int -> int))
           (set_flag_add_282:bool) (s_add_x_277:int) (s_add_y_278:int)
           (xs:int) : int =
  if xs = 0
  then
    0
  else
    f set_flag_add_282 s_add_x_277 s_add_y_278 (Random.int 0) +
    map
      set_flag_add_282 s_add_x_277 s_add_y_278
      (0 * xs + (0 * f_EXPARAM_121 + 0)) set_flag_add_282 s_add_x_277
      s_add_y_278 f set_flag_add_282 s_add_x_277 s_add_y_278 (xs - 1)
let compose (_:bool) (_:int) (_:int) (_:int) (_:bool) (_:int) (_:int)
           (f:(bool -> int -> int -> int -> int)) (_:bool) (_:int) (_:int)
           (_:int) (_:bool) (_:int) (_:int)
           (g:(bool -> int -> int -> int -> int)) (set_flag_add_282:bool)
           (s_add_x_277:int) (s_add_y_278:int) (x:int) : int =
  f
    set_flag_add_282 s_add_x_277 s_add_y_278
    (g set_flag_add_282 s_add_x_277 s_add_y_278 x)
let rec add (x_DO_NOT_CARE_295:bool) (x_DO_NOT_CARE_296:int)
           (x_DO_NOT_CARE_297:int) (x:int) (prev_set_flag_add_281:bool)
           (s_prev_add_x_279:int) (s_prev_add_y_280:int) (y:int) : int =
  if prev_set_flag_add_281 then assert false;
  add_without_checking_293
    x_DO_NOT_CARE_295 x_DO_NOT_CARE_296 x_DO_NOT_CARE_297 x
    prev_set_flag_add_281 s_prev_add_x_279 s_prev_add_y_280 y
and add_without_checking_293 (_:bool) (_:int) (_:int) (x:int) (_:bool)
                            (_:int) (_:int) (y:int) : int =
  let set_flag_add_282 : bool = true
  in
  let s_add_y_278 : int = y
  in
  let s_add_x_277 : int = x
  in
  x + y
let main (set_flag_add_282:bool) (s_add_x_277:int) (s_add_y_278:int)
        (():unit) : int =
  let l : int = Random.int 0
  in
  if l >= 0
  then
    map
      set_flag_add_282 s_add_x_277 s_add_y_278 0 set_flag_add_282
      s_add_x_277 s_add_y_278
      (compose
        set_flag_add_282 s_add_x_277 s_add_y_278 0 set_flag_add_282
        s_add_x_277 s_add_y_278
        (add set_flag_add_282 s_add_x_277 s_add_y_278 1) set_flag_add_282
        s_add_x_277 s_add_y_278 0 set_flag_add_282 s_add_x_277
        s_add_y_278
        (add_without_checking_293
          set_flag_add_282 s_add_x_277 s_add_y_278 2))
      set_flag_add_282 s_add_x_277 s_add_y_278 l
  else
    0
let u_20280 : int = main false 0 0 ()
