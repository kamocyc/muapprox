(* int, int -> ('a -> 'b) -> 'b *)

let pair f s k_ =
  k_ (fun k -> k f s)

let cons a len_l k =
  len_l (fun len l ->
    pair (len + 1) (fun i k -> if i = 0 then k a else l (i - 1) k) k
  )
let hd len_l k = len_l (fun len l -> l 0 k)
let tl len_l k = len_l (fun len l -> pair (len - 1) (fun i k2 -> l (i + 1) k2) k)
let is_nil len_l k = len_l (fun len l -> if len = 0 then k 1 else k 0)

let rec append len_l1 len_l2 k =
  is_nil len_l1 (fun b ->
    if b = 1 then
      k len_l2
    else
      tl len_l1 (fun len_l1' ->
        append len_l1' len_l2 (fun ls_rec ->
          hd len_l1 (fun a ->
            cons a ls_rec k
          )
        )
      )
  )

let rec length_cps (k : int -> unit) len_l =
  is_nil len_l (fun b ->
    if b = 1 then
      k 0
    else
      tl len_l (fun len_l' ->
        length_cps
          (fun rlen -> k (rlen + 1))
          len_l'
      )
  )

let main ls1 ls2 =
  append
    ls1
    ls2
    (fun len_l ->
      length_cps
        (fun rlen ->
          len_l (fun len _ -> 
            ls1 (fun len1 _ ->
              ls2 (fun len2 _ ->
                assert (len <= len1 + len2)
              )
            )
          )
        )
        len_l
    )

let () =
  let x = read_int () in
  let y = read_int () in
  if x >= 0 && y >= 0 then
    pair x (fun i k -> k true) (fun ls1 ->
      pair y (fun i k -> k false) (fun ls2 ->
        main ls1 ls2
      )
    )
  else
    ()
  
(* 
let cons a len l k =
  k (len + 1) (fun i k -> if i = 0 then k a else l (i - 1) k)
let hd len l k = l 0 k
let tl len l k = k (len - 1) (fun i k -> l (i + 1) k)
let is_nil len l k = if len = 0 then k 1 else k 0

let rec append len1 l1 len2 l2 k =
  is_nil len1 l1 (fun b ->
    if b = 1 then
      k len2 l2
    else
      tl len1 l1 (fun len1' l1' ->
        append len1' l1' len2 l2 (fun len l ->
          hd len1 l1 (fun a ->
            cons a len l k
          )
        )
      )
  )

let rec length_cps k len l =
  is_nil len l (fun b ->
    if b = 1 then
      k 0
    else
      tl len l (fun len' l' ->
        length_cps
          (fun rlen -> k (rlen + 1))
          len' l'
      )
  )

let main ls1 ls2 =
  ls1 (fun len1 l1 ->
    ls2 (fun len2 l2 ->
      append
        len1
        l1
        len2
        l2
        (fun len l ->
          length_cps
            (fun rlen -> assert (len <= len1 + len2))
            len
            l
        )
    )
  )

let () =
  let x = read_int () in
  let y = read_int () in
  if x >= 0 && y >= 0 then
    let ls1 = (fun k -> k x (fun i k -> k true)) in
    let ls2 = (fun k -> k y (fun i k -> k false)) in
    main ls1 ls2
  else
    () *)

(* let cons a len l k =
  k (len + 1) (fun i k -> if i = 0 then k a else l (i - 1) k)
let hd len l k = l 0 k
let tl len l k = k (len - 1) (fun i k -> l (i + 1) k)
let is_nil len l k = if len = 0 then k 1 else k 0

let rec append len1 l1 len2 l2 k =
  is_nil len1 l1 (fun b ->
    if b = 1 then
      k len2 l2
    else
      tl len1 l1 (fun len1' l1' ->
        append len1' l1' len2 l2 (fun len l ->
          hd len1 l1 (fun a ->
            cons a len l k
          )
        )
      )
  )

let rec length_cps k len l =
  is_nil len l (fun b ->
    if b = 1 then
      k 0
    else
      tl len l (fun len' l' ->
        length_cps
          (fun rlen -> k (rlen + 1))
          len' l'
      )
  )

let main len1 len2 =
  append
    len1 (fun i k -> k true)
    len2 (fun i k -> k false)
    (fun len l ->
      length_cps
        (fun rlen -> assert (len <= len1 + len2))
        len
        l
    )

let () =
  let x = read_int () in
  let y = read_int () in
  if x >= 0 && y >= 0 then
    main x y
  else
    ()  *)

(* 
let cons a (len, l) =
  (len + 1, fun i -> if i = 0 then a else l (i - 1))
let hd (len, l) = l 0
let tl (len, l) = (len - 1, fun i -> l (i + 1))
let is_nil (len, l) = len = 0

let rec append xs1 xs2 =
  if is_nil xs1 then
    xs2
  else
    let xs = append (tl xs1) xs2 in
    cons (hd xs1) xs
let rec length_cps k xs =
  if is_nil xs then
    k 0
  else
    length_cps
      (fun len -> k (len + 1))
      (tl xs)
let main len1 len2 =
  length_cps
    (fun len -> assert (len <= len1 + len2))
    (append (len1, fun i -> true) (len2, fun i -> false))

let () = main (read_int ()) (read_int ()) *)
