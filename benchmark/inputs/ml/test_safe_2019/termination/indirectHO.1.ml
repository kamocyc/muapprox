let rec id (prev_set_flag_id_86:bool) (x:unit) : unit =
  if prev_set_flag_id_86 then assert false;
  id_without_checking_113 prev_set_flag_id_86 x
and id_without_checking_113 (_:bool) (x:unit) : unit =
  let set_flag_id_87 : bool = true
  in
  x
let app (_:bool) (_:int) (_:bool)
       (h:(bool -> unit -> bool -> unit -> unit)) (set_flag_id_87:bool)
       (v:unit) : unit = h set_flag_id_87 () set_flag_id_87 v
let rec f (_:bool) (n:int) (set_flag_id_87:bool) (():unit) : (bool ->
                                                                unit ->
                                                                  unit) =
  if n > 0
  then
    app
      set_flag_id_87 (0 * n + 0) set_flag_id_87
      (f set_flag_id_87 (n - 1))
  else
    id
let main (set_flag_id_87:bool) (():unit) : unit =
  f set_flag_id_87 (Random.int 0) set_flag_id_87 () set_flag_id_87 ()
let u_397 : unit = main false ()
