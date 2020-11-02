let rec succ (x_DO_NOT_CARE_318:bool) (x_DO_NOT_CARE_319:int)
            (x_DO_NOT_CARE_320:int) (x_DO_NOT_CARE_321:int)
            (m_EXPARAM_238:int) (x_DO_NOT_CARE_314:bool)
            (x_DO_NOT_CARE_315:int) (x_DO_NOT_CARE_316:int)
            (x_DO_NOT_CARE_317:int)
            (m:(bool ->
                  int ->
                    int ->
                      int ->
                        int ->
                          bool ->
                            int ->
                              int ->
                                int ->
                                  (bool -> int -> int -> int -> int -> int) ->
                                    bool -> int -> int -> int -> int -> int))
            (x_DO_NOT_CARE_310:bool) (x_DO_NOT_CARE_311:int)
            (x_DO_NOT_CARE_312:int) (x_DO_NOT_CARE_313:int)
            (s_EXPARAM_240:int) (x_DO_NOT_CARE_306:bool)
            (x_DO_NOT_CARE_307:int) (x_DO_NOT_CARE_308:int)
            (x_DO_NOT_CARE_309:int)
            (s:(bool -> int -> int -> int -> int -> int))
            (prev_set_flag_succ_259:bool) (s_prev_succ_m_EXPARAM_254:int)
            (s_prev_succ_s_EXPARAM_256:int) (s_prev_succ_z_258:int) (
            z:int) : int =
  if prev_set_flag_succ_259
  then
    if
      1 + s_prev_succ_s_EXPARAM_256 > 1 + s_EXPARAM_240 &&
      1 + s_EXPARAM_240 >= 0
    then
      ()
    else
      assert false;
  succ_without_checking_304
    x_DO_NOT_CARE_318 x_DO_NOT_CARE_319 x_DO_NOT_CARE_320 x_DO_NOT_CARE_321
    m_EXPARAM_238 x_DO_NOT_CARE_314 x_DO_NOT_CARE_315 x_DO_NOT_CARE_316
    x_DO_NOT_CARE_317 m x_DO_NOT_CARE_310 x_DO_NOT_CARE_311 x_DO_NOT_CARE_312
    x_DO_NOT_CARE_313 s_EXPARAM_240 x_DO_NOT_CARE_306 x_DO_NOT_CARE_307
    x_DO_NOT_CARE_308 x_DO_NOT_CARE_309 s prev_set_flag_succ_259
    s_prev_succ_m_EXPARAM_254 s_prev_succ_s_EXPARAM_256 s_prev_succ_z_258 
    z
and succ_without_checking_304 (_:bool) (_:int) (_:int) (_:int)
                             (m_EXPARAM_238:int) (_:bool) (_:int) (_:int)
                             (_:int)
                             (m:(bool ->
                                   int ->
                                     int ->
                                       int ->
                                         int ->
                                           bool ->
                                             int ->
                                               int ->
                                                 int ->
                                                   (bool ->
                                                      int ->
                                                        int ->
                                                          int -> int -> int) ->
                                                     bool ->
                                                       int ->
                                                         int ->
                                                           int -> int -> int))
                             (_:bool) (_:int) (_:int) (_:int)
                             (s_EXPARAM_240:int) (_:bool) (_:int) (_:int)
                             (_:int)
                             (s:(bool -> int -> int -> int -> int -> int))
                             (_:bool) (_:int) (_:int) (_:int) (z:int) : 
  int =
  let set_flag_succ_260 : bool = true
  in
  let s_succ_z_253 : int = z
  in
  let s_succ_s_EXPARAM_251 : int = s_EXPARAM_240
  in
  let s_succ_m_EXPARAM_249 : int = m_EXPARAM_238
  in
  m
    set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    (0 * z + (2 * s_EXPARAM_240 + (0 * m_EXPARAM_238 + (-8))))
    set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    s set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
    s_succ_z_253
    (s
      set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
      s_succ_z_253 z)
let id (_:bool) (_:int) (_:int) (_:int) (x:int) : int = x
let two (_:bool) (_:int) (_:int) (_:int) (f_EXPARAM_212:int) (_:bool) 
       (_:int) (_:int) (_:int)
       (f:(bool ->
             int ->
               int ->
                 int ->
                   int ->
                     bool ->
                       int ->
                         int ->
                           int ->
                             (bool ->
                                int ->
                                  int ->
                                    int ->
                                      int ->
                                        bool ->
                                          int ->
                                            int ->
                                              int ->
                                                (bool ->
                                                   int ->
                                                     int -> int -> int -> int) ->
                                                  bool ->
                                                    int ->
                                                      int ->
                                                        int -> int -> int) ->
                               bool ->
                                 int ->
                                   int ->
                                     int ->
                                       int ->
                                         bool ->
                                           int ->
                                             int ->
                                               int ->
                                                 (bool ->
                                                    int ->
                                                      int ->
                                                        int -> int -> int) ->
                                                   bool ->
                                                     int ->
                                                       int ->
                                                         int -> int -> int))
       (_:bool) (_:int) (_:int) (_:int) (z_EXPARAM_216:int)
       (set_flag_succ_260:bool) (s_succ_m_EXPARAM_249:int)
       (s_succ_s_EXPARAM_251:int) (s_succ_z_253:int)
       (z:(bool ->
             int ->
               int ->
                 int ->
                   int ->
                     bool ->
                       int ->
                         int ->
                           int ->
                             (bool -> int -> int -> int -> int -> int) ->
                               bool -> int -> int -> int -> int -> int)) : 
  (bool ->
     int ->
       int ->
         int ->
           int ->
             bool ->
               int ->
                 int ->
                   int ->
                     (bool -> int -> int -> int -> int -> int) ->
                       bool -> int -> int -> int -> int -> int) =
  f
    set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    ((-5) * z_EXPARAM_216 + ((-8) * f_EXPARAM_212 + 1)) set_flag_succ_260
    s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    (f
      set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
      s_succ_z_253 (7 * z_EXPARAM_216 + (6 * f_EXPARAM_212 + 1))
      set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
      s_succ_z_253 z)
let zero (_:bool) (_:int) (_:int) (_:int) (_:int) (_:bool) (_:int) (_:int)
        (_:int) (_:(bool -> int -> int -> int -> int -> int)) (_:bool)
        (_:int) (_:int) (_:int) (z:int) : int = z
let main (set_flag_succ_260:bool) (s_succ_m_EXPARAM_249:int)
        (s_succ_s_EXPARAM_251:int) (s_succ_z_253:int) (():unit) : int =
  two
    set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    (-8) set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
    s_succ_z_253 succ set_flag_succ_260 s_succ_m_EXPARAM_249
    s_succ_s_EXPARAM_251 s_succ_z_253 (-1) set_flag_succ_260
    s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253 zero
    set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251 s_succ_z_253
    7 set_flag_succ_260 s_succ_m_EXPARAM_249 s_succ_s_EXPARAM_251
    s_succ_z_253 id set_flag_succ_260 s_succ_m_EXPARAM_249
    s_succ_s_EXPARAM_251 s_succ_z_253 0
let u_13055 : int = main false 0 0 0 ()
