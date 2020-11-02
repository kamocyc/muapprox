let rec id (prev_set_flag_id_79:bool) (s_prev_id_x_78:int) (x:int) : 
  int =
  if prev_set_flag_id_79 then assert false;
  id_without_checking_107 prev_set_flag_id_79 s_prev_id_x_78 x
and id_without_checking_107 (_:bool) (_:int) (x:int) : int =
  let set_flag_id_80 : bool = true
  in
  let s_id_x_77 : int = x
  in
  x
let rec omega (set_flag_id_80:bool) (s_id_x_77:int) (x:int) : int =
  omega set_flag_id_80 s_id_x_77 x
let f (_:bool) (_:int) (_:int) (_:bool) (_:int)
     (_:(bool -> int -> int -> int)) (_:bool) (_:int) (_:int) (_:bool)
     (_:int) (y:(bool -> int -> int -> int)) (set_flag_id_80:bool)
     (s_id_x_77:int) (z:int) : int = y set_flag_id_80 s_id_x_77 z
let u_597 : int =
  f
    false 0 0 false 0 (f false 0 0 false 0 id false 0 0 false 0 omega)
    false 0 0 false 0 id_without_checking_107 false 0 1
