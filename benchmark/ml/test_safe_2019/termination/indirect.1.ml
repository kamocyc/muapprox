let rec id (prev_set_flag_id_82:bool) (x:unit) : unit =
  if prev_set_flag_id_82 then assert false;
  id_without_checking_109 prev_set_flag_id_82 x
and id_without_checking_109 (_:bool) (x:unit) : unit =
  let set_flag_id_83 : bool = true
  in
  x
let app (_:bool) (_:int) (_:bool)
       (h:(bool -> int -> bool -> unit -> unit)) (_:bool) (v:int)
       (set_flag_id_83:bool) (u:unit) : unit =
  h set_flag_id_83 v set_flag_id_83 u
let rec f (set_flag_id_83:bool) (x:int) : (bool -> unit -> unit) =
  if x > 0
  then
    app
      set_flag_id_83 (0 * x + 0) set_flag_id_83 f set_flag_id_83 (x - 1)
  else
    id
let main (set_flag_id_83:bool) (():unit) : unit =
  f set_flag_id_83 (Random.int 0) set_flag_id_83 ()
let u_395 : unit = main false ()
