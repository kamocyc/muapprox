(* katsura-solverで型が付かないため解けない *)
let rec loop () = loop ()
let myassert b = if b then () else loop ()
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
let main () =
  let len1 = read_int () in
  let len2 = read_int () in
  (* 元のプログラムではlen >= 0の暗黙の仮定があると思われるので、条件を追加 *)
  if len1 >= 0 && len2 >= 0 then
    length_cps
      (fun len -> myassert (len <= len1 + len2))
      (append (len1, fun i -> true) (len2, fun i -> false))
  else ()