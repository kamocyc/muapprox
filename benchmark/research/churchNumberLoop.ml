let rec succ m s z = m s (s z)
let rec zero f z = z
let rec one f z = f z
let rec plus m n s z = m s (n s z)
let rec mult m n s z = m (n s) z

let add x = x + 1
let toNum c =
  c add 0

let rec loop n k =
  if n > 0 then loop (n - 1) k
  else k ()

let () =
  let a = plus one one in
  let a = mult a a in
  let a = mult a a in
  let a = mult a a in
  let n = toNum a in
  loop n (fun () -> print_int n)

(* polymorphic typeは現状できないので、必ず型としてintが現れる。
 その場合でも、関数の適用回数が再帰回数になるので扱いが大変 *)
(* 機械的にCPS変換をすることで、HFLzに変換は可能 *)
