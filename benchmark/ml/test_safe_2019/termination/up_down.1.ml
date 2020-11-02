let rec app (_:bool) (_:int) (_:int) (_:bool) (_:int)
           (f:(bool -> int -> int -> unit)) (set_flag_up_86:bool)
           (s_up_x_83:int) (x:int) : unit = f set_flag_up_86 s_up_x_83 x
and down (set_flag_up_86:bool) (s_up_x_83:int) (x:int) : unit =
  if x = 0 then () else down set_flag_up_86 s_up_x_83 (x - 1)
and up (prev_set_flag_up_85:bool) (s_prev_up_x_84:int) (x:int) : unit =
  if prev_set_flag_up_85 then assert false;
  up_without_checking_112 prev_set_flag_up_85 s_prev_up_x_84 x
and up_without_checking_112 (_:bool) (_:int) (x:int) : unit =
  let set_flag_up_86 : bool = true
  in
  let s_up_x_83 : int = x
  in
  if x = 0
  then
    ()
  else
    up_without_checking_112 set_flag_up_86 s_up_x_83 (x + 1)
let main (set_flag_up_86:bool) (s_up_x_83:int) (():unit) : unit =
  let t1 : int = Random.int 0
  in
  let t2 : int = Random.int 0
  in
  if t1 > 0
  then
    app
      set_flag_up_86 s_up_x_83 0 set_flag_up_86 s_up_x_83 down
      set_flag_up_86 s_up_x_83 t1
  else
    (if t2 < 0
     then
       app
         set_flag_up_86 s_up_x_83 0 set_flag_up_86 s_up_x_83 up
         set_flag_up_86 s_up_x_83 t2)
let u_443 : unit = main false 0 ()
