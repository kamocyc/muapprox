let nil k = k 0 (fun i k -> assert false)
let cons a len l k =
  k (len + 1) (fun i k -> if i = 0 then k a else l (i - 1) k)
let hd len l k = l 0 k
let tl len l k = k (len - 1) (fun i k -> l (i + 1) k)
let is_nil len l k = if len = 0 then k 1 else k 0

let rec insert (x:int) ys_l ys_len k =
  is_nil ys_l ys_len (fun b ->
    if b = 1 then
      nil (fun nlen nl -> cons x nlen nl k)
    else
      hd ys_l ys_len (fun x' ->
        if x <= x' then
          cons x ys_l ys_len k
        else
          hd ys_l ys_len (fun x'' ->
            tl ys_l ys_len (fun l' len' ->
              insert x l' len' (fun l1 len1 ->
                cons x'' l1 len1 k
              )
            )
          )
      )
  )

let rec isort xs_l xs_len k =
  is_nil xs_l xs_len (fun b ->
    if b = 1 then
      nil k
    else  
      hd xs_l xs_len (fun a ->
        tl xs_l xs_len (fun l1 len1 ->
          isort l1 len1 (fun l2 len2 ->
            insert a l2 len2 k
          )
        )
      )
  )

let rec make_list n k =
  if n = 0 then
    nil k
  else
    make_list
      (n - 1)
      (fun l len ->
        cons n l len k
      )

(* let rec ordered xs_l xs_len k =
  is_nil xs_l xs_len (fun b ->
    if b = 1 then
      true
    else if is_nil (tl xs) then
      true
    else
      hd xs <= hd (tl xs) && ordered (tl xs)
  ) *)

(* let main len = assert (ordered (isort (len, fun i -> len - i))) *)
let main len k =
  isort len (fun i k2 -> k2 (len - i)) k

let () =
  let len = read_int () in
  main len (fun l len ->
    ()
  )