let rec zip (x_DO_NOT_CARE_73:bool) (x_DO_NOT_CARE_74:int)
           (x_DO_NOT_CARE_75:int) (xs:int) (prev_set_flag_zip_56:bool)
           (s_prev_zip_xs_54:int) (s_prev_zip_ys_55:int) (ys:int) : int =
  if prev_set_flag_zip_56
  then
    if s_prev_zip_xs_54 > xs && xs >= 0 then () else assert false;
  zip_without_checking_71
    x_DO_NOT_CARE_73 x_DO_NOT_CARE_74 x_DO_NOT_CARE_75 xs
    prev_set_flag_zip_56 s_prev_zip_xs_54 s_prev_zip_ys_55 ys
and zip_without_checking_71 (_:bool) (_:int) (_:int) (xs:int)
                           (_:bool) (_:int) (_:int) (ys:int) : int =
  let set_flag_zip_57 : bool = true
  in
  let s_zip_ys_53 : int = ys
  in
  let s_zip_xs_52 : int = xs
  in
  if xs <= 0
  then
    0
  else
    let xs_prime_ : int = xs - 1
    in
    if ys <= 0
    then
      0
    else
      let ys_prime_ : int = ys - 1
      in
      1 +
      zip_without_checking_71
        set_flag_zip_57 s_zip_xs_52 s_zip_ys_53 xs_prime_
        set_flag_zip_57 s_zip_xs_52 s_zip_ys_53 ys_prime_
let main (set_flag_zip_57:bool) (s_zip_xs_52:int) (s_zip_ys_53:int)
        (():unit) : int =
  let l1 : int = Random.int 0
  in
  let l2 : int = Random.int 0
  in
  zip
    set_flag_zip_57 s_zip_xs_52 s_zip_ys_53 l1 set_flag_zip_57
    s_zip_xs_52 s_zip_ys_53 l2
let u_2572 : int = main false 0 0 ()
