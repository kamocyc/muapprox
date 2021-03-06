let rec gt (x_DO_NOT_CARE_93:bool) (x_DO_NOT_CARE_94:int)
          (x_DO_NOT_CARE_95:int) (lb:int) (prev_set_flag_gt_71:bool)
          (s_prev_gt_lb_69:int) (s_prev_gt_n_70:int) (n:int) : bool =
  if prev_set_flag_gt_71 then assert false;
  gt_without_checking_91
    x_DO_NOT_CARE_93 x_DO_NOT_CARE_94 x_DO_NOT_CARE_95 lb
    prev_set_flag_gt_71 s_prev_gt_lb_69 s_prev_gt_n_70 n
and gt_without_checking_91 (_:bool) (_:int) (_:int) (lb:int) (_:bool)
                          (_:int) (_:int) (n:int) : bool =
  let set_flag_gt_72 : bool = true
  in
  let s_gt_n_68 : int = n
  in
  let s_gt_lb_67 : int = lb
  in
  n > lb
let rec f (_:bool) (_:int) (_:int) (x:int) (_:bool) (_:int) (_:int)
         (p_EXPARAM_61:int) (set_flag_gt_72:bool) (s_gt_lb_67:int)
         (s_gt_n_68:int) (p:(bool -> int -> int -> int -> bool)) : unit =
  if p set_flag_gt_72 s_gt_lb_67 s_gt_n_68 x
  then
    f
      set_flag_gt_72 s_gt_lb_67 s_gt_n_68 (x - 1) set_flag_gt_72
      s_gt_lb_67 s_gt_n_68 (0 * p_EXPARAM_61 + (0 * x + 0))
      set_flag_gt_72 s_gt_lb_67 s_gt_n_68 p
let u_536 : unit =
  f false 0 0 (Random.int 0) false 0 0 0 false 0 0 (gt false 0 0 0)
