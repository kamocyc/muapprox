let id (_:bool) (_:int) (x:int) : int = x
let rec omega (prev_set_flag_omega_121:bool) (s_prev_omega_x_120:int) (x:int) : 
  int =
  if prev_set_flag_omega_121 then assert false;
  omega_without_checking_143 prev_set_flag_omega_121 s_prev_omega_x_120 x
and omega_without_checking_143 (_:bool) (_:int) (x:int) : int =
  let set_flag_omega_122 : bool = true
  in
  let s_omega_x_119 : int = x
  in
  omega_without_checking_143 set_flag_omega_122 s_omega_x_119 x
let f (_:bool) (_:int) (_:int) (_:bool) (_:int)
     (_:(bool -> int -> int -> int)) (_:bool) (_:int) (_:int) (_:bool)
     (_:int) (y:(bool -> int -> int -> int)) (set_flag_omega_122:bool)
     (s_omega_x_119:int) (z:int) : int =
  y set_flag_omega_122 s_omega_x_119 z
let u_3275 : int =
  f
    false 0 0 false 0 (f false 0 0 false 0 id false 0 0 false 0 omega)
    false 0 0 false 0 id false 0 1
