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

let () = main (read_int ()) (read_int ()) 