(* katsura-solverで型が付かないため解けない *)
let rec loop () = loop ()
let myassert b = if b then () else loop ()
let hd (len, l) = l 0
let tl (len, l) = (len - 1, fun i -> l (i + 1))
let is_nil (len, l) = len = 0

let rec for_all f xs =
  if is_nil xs then
    true
  else
    f (hd xs) && for_all f (tl xs)
let main () =
  let len = read_int () in
  (* 元のプログラムではlen >= 0の暗黙の仮定があると思われるので、条件を追加 *)
  if len >= 0 then
    myassert (for_all (fun x -> x <= len) (len, fun i -> len - i))
  else ()
