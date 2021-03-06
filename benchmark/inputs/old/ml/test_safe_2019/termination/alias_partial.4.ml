let rec f (prev_set_flag_f_79:bool) (s_prev_f_x_78:int) (x:int) : (bool ->
                                                                    int ->
                                                                    int ->
                                                                    int) =
  if prev_set_flag_f_79
  then
    if s_prev_f_x_78 > x && x >= 0 then () else assert false;
  f_without_checking_89 prev_set_flag_f_79 s_prev_f_x_78 x
and f_without_checking_89 (_:bool) (_:int) (x:int) : (bool ->
                                                        int ->
                                                          int -> int) =
  let set_flag_f_80 : bool = true
  in
  let s_f_x_77 : int = x
  in
  if x > 0
  then
    f_without_checking_89 set_flag_f_80 s_f_x_77 (x - 1)
  else
    lambda
and lambda (_:bool) (_:int) (x:int) : int = x + 1
let g : (bool -> int -> int -> int) = f false 0 1
let main (set_flag_f_80:bool) (s_f_x_77:int) (():unit) : int =
  g set_flag_f_80 s_f_x_77 2
let u_3091 : int = main false 0 ()
