let rec sum (prev_set_flag_sum_26:bool) (_:int) (n:int) (k_sum_168:(int -> X)) : X =
         let u_35 (k_sum_u_184:(unit -> X)) : X =
           if prev_set_flag_sum_26 then <|fail|> () (fun (():unit) -> ⊥) else k_sum_u_184 ()
         in
         u_35
           (fun (():unit) ->
              if n <= 0 then k_sum_168 0 else sum true 0 (n - 1) (fun (x_190:int) -> k_sum_168 (n + x_190)))
       in
       let u_59 (k_u_231:(int -> X)) : X =
         rand_int_cps () (fun (x_236:int) -> sum false 0 x_236 k_u_231)
       in
       u_59 (fun (_:int) -> {end})