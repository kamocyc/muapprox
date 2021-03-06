let rec qs (_:bool) (_:int) (_:int) (_:int) (_:int) (_:int)
          (cmp_EXPARAM_196:int) (_:bool) (_:int) (_:int) (_:int) (_:int)
          (_:int)
          (cmp:(bool ->
                  int ->
                    int ->
                      int ->
                        int ->
                          int ->
                            int ->
                              bool ->
                                int ->
                                  int -> int -> int -> int -> int -> bool))
          (set_flag_par_245:bool) (s_par_cmp_EXPARAM_232:int)
          (s_par_x_234:int) (s_par_l_235:int) (s_par_r_236:int)
          (s_par_xs_237:int) (n:int) : int =
  if n <= 0
  then
    0
  else
    let xs_prime_ : int = n - 1
    in
    par
      set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
      s_par_r_236 s_par_xs_237 (0 * n + (0 * cmp_EXPARAM_196 + 0))
      set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
      s_par_r_236 s_par_xs_237 cmp set_flag_par_245 s_par_cmp_EXPARAM_232
      s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 (Random.int 0)
      set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
      s_par_r_236 s_par_xs_237 0 set_flag_par_245 s_par_cmp_EXPARAM_232
      s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 0 set_flag_par_245
      s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237
      xs_prime_
and par (x_DO_NOT_CARE_311:bool) (x_DO_NOT_CARE_312:int)
       (x_DO_NOT_CARE_313:int) (x_DO_NOT_CARE_314:int)
       (x_DO_NOT_CARE_315:int) (x_DO_NOT_CARE_316:int) (cmp_EXPARAM_202:int)
       (x_DO_NOT_CARE_305:bool) (x_DO_NOT_CARE_306:int)
       (x_DO_NOT_CARE_307:int) (x_DO_NOT_CARE_308:int)
       (x_DO_NOT_CARE_309:int) (x_DO_NOT_CARE_310:int)
       (cmp:(bool ->
               int ->
                 int ->
                   int ->
                     int ->
                       int ->
                         int ->
                           bool ->
                             int -> int -> int -> int -> int -> int -> bool))
       (x_DO_NOT_CARE_299:bool) (x_DO_NOT_CARE_300:int)
       (x_DO_NOT_CARE_301:int) (x_DO_NOT_CARE_302:int)
       (x_DO_NOT_CARE_303:int) (x_DO_NOT_CARE_304:int) (x:int)
       (x_DO_NOT_CARE_293:bool) (x_DO_NOT_CARE_294:int)
       (x_DO_NOT_CARE_295:int) (x_DO_NOT_CARE_296:int)
       (x_DO_NOT_CARE_297:int) (x_DO_NOT_CARE_298:int) (l:int)
       (x_DO_NOT_CARE_287:bool) (x_DO_NOT_CARE_288:int)
       (x_DO_NOT_CARE_289:int) (x_DO_NOT_CARE_290:int)
       (x_DO_NOT_CARE_291:int) (x_DO_NOT_CARE_292:int) (r:int)
       (prev_set_flag_par_244:bool) (s_prev_par_cmp_EXPARAM_238:int)
       (s_prev_par_x_240:int) (s_prev_par_l_241:int) (s_prev_par_r_242:int)
       (s_prev_par_xs_243:int) (xs:int) : int =
  if prev_set_flag_par_244
  then
    if
      s_prev_par_r_242 > r && r >= 0 ||
      s_prev_par_r_242 >= r && (s_prev_par_l_241 > l && l >= 0)
    then
      ()
    else
      assert false;
  par_without_checking_285
    x_DO_NOT_CARE_311 x_DO_NOT_CARE_312 x_DO_NOT_CARE_313 x_DO_NOT_CARE_314
    x_DO_NOT_CARE_315 x_DO_NOT_CARE_316 cmp_EXPARAM_202 x_DO_NOT_CARE_305
    x_DO_NOT_CARE_306 x_DO_NOT_CARE_307 x_DO_NOT_CARE_308 x_DO_NOT_CARE_309
    x_DO_NOT_CARE_310 cmp x_DO_NOT_CARE_299 x_DO_NOT_CARE_300
    x_DO_NOT_CARE_301 x_DO_NOT_CARE_302 x_DO_NOT_CARE_303 x_DO_NOT_CARE_304 
    x x_DO_NOT_CARE_293 x_DO_NOT_CARE_294 x_DO_NOT_CARE_295 x_DO_NOT_CARE_296
    x_DO_NOT_CARE_297 x_DO_NOT_CARE_298 l x_DO_NOT_CARE_287 x_DO_NOT_CARE_288
    x_DO_NOT_CARE_289 x_DO_NOT_CARE_290 x_DO_NOT_CARE_291 x_DO_NOT_CARE_292 
    r prev_set_flag_par_244 s_prev_par_cmp_EXPARAM_238 s_prev_par_x_240
    s_prev_par_l_241 s_prev_par_r_242 s_prev_par_xs_243 xs
and par_without_checking_285 (_:bool) (_:int) (_:int) (_:int) (_:int) 
                            (_:int) (cmp_EXPARAM_202:int) (_:bool) (_:int)
                            (_:int) (_:int) (_:int) (_:int)
                            (cmp:(bool ->
                                    int ->
                                      int ->
                                        int ->
                                          int ->
                                            int ->
                                              int ->
                                                bool ->
                                                  int ->
                                                    int ->
                                                      int ->
                                                        int ->
                                                          int -> int -> bool))
                            (_:bool) (_:int) (_:int) (_:int) (_:int) 
                            (_:int) (x:int) (_:bool) (_:int) (_:int) 
                            (_:int) (_:int) (_:int) (l:int) (_:bool) 
                            (_:int) (_:int) (_:int) (_:int) (_:int) (r:int)
                            (_:bool) (_:int) (_:int) (_:int) (_:int) 
                            (_:int) (xs:int) : int =
  let set_flag_par_245 : bool = true
  in
  let s_par_xs_237 : int = xs
  in
  let s_par_r_236 : int = r
  in
  let s_par_l_235 : int = l
  in
  let s_par_x_234 : int = x
  in
  let s_par_cmp_EXPARAM_232 : int = cmp_EXPARAM_202
  in
  if xs <= 0
  then
    qs
      set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
      s_par_r_236 s_par_xs_237
      (0 * xs + (0 * r + (0 * l + (0 * x + (0 * cmp_EXPARAM_202 + 0)))))
      set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
      s_par_r_236 s_par_xs_237 cmp set_flag_par_245 s_par_cmp_EXPARAM_232
      s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 l
    +
    (1 +
     qs
       set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
       s_par_r_236 s_par_xs_237
       (0 * xs + (0 * r + (0 * l + (0 * x + (0 * cmp_EXPARAM_202 + 0)))))
       set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
       s_par_r_236 s_par_xs_237 cmp set_flag_par_245 s_par_cmp_EXPARAM_232
       s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 r)
  else
    let x_prime_ : int = Random.int 0
    in
    let xs_prime_ : int = xs - 1
    in
    if
      cmp
        set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
        s_par_r_236 s_par_xs_237 x_prime_ set_flag_par_245
        s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236
        s_par_xs_237 x
    then
      par_without_checking_285
        set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
        s_par_r_236 s_par_xs_237
        (0 * xs + (0 * r + (0 * l + (0 * x + (0 * cmp_EXPARAM_202 + 0)))))
        set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
        s_par_r_236 s_par_xs_237 cmp set_flag_par_245 s_par_cmp_EXPARAM_232
        s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 x set_flag_par_245
        s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236
        s_par_xs_237 (1 + l) set_flag_par_245 s_par_cmp_EXPARAM_232
        s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 r set_flag_par_245
        s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236
        s_par_xs_237 xs_prime_
    else
      par_without_checking_285
        set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
        s_par_r_236 s_par_xs_237
        (0 * xs + (0 * r + (0 * l + (0 * x + (0 * cmp_EXPARAM_202 + 0)))))
        set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
        s_par_r_236 s_par_xs_237 cmp set_flag_par_245 s_par_cmp_EXPARAM_232
        s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 x set_flag_par_245
        s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236
        s_par_xs_237 l set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234
        s_par_l_235 s_par_r_236 s_par_xs_237 (1 + r) set_flag_par_245
        s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236
        s_par_xs_237 xs_prime_
let cmp (_:bool) (_:int) (_:int) (_:int) (_:int) (_:int) (x:int) (_:bool)
       (_:int) (_:int) (_:int) (_:int) (_:int) (y:int) : bool = x >= y
let main (set_flag_par_245:bool) (s_par_cmp_EXPARAM_232:int)
        (s_par_x_234:int) (s_par_l_235:int) (s_par_r_236:int)
        (s_par_xs_237:int) (():unit) : int =
  let n : int = Random.int 0
  in
  qs
    set_flag_par_245 s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235
    s_par_r_236 s_par_xs_237 0 set_flag_par_245 s_par_cmp_EXPARAM_232
    s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 cmp set_flag_par_245
    s_par_cmp_EXPARAM_232 s_par_x_234 s_par_l_235 s_par_r_236 s_par_xs_237 
    n
let u_44547 : int = main false 0 0 0 0 0 ()
