let rec qs (cmp : int -> int -> bool) n (k : int -> unit) : unit =
  if n <= 0 then
    k 0
  else
    let xs' = n - 1 in
    par cmp (read_int ()) 0 0 xs' k

and  par (cmp : int -> int -> bool) x l r xs (k : int -> unit) : unit=
  (* ここで(xs + l + r, xs) がranking function (lexicographc order) *)
  if xs <= 0 then
    qs cmp l (fun r' -> qs cmp r (fun r'' -> k (r' + 1 + r'')))
  else
    if cmp (read_int ()) x then
      par cmp x (1 + l) r (xs - 1) k
    else
      par cmp x l (1 + r) (xs - 1) k
  
let cmp (x : int) (y : int) = x >= y

let () =
  let n = read_int () in
  qs cmp n (fun r -> print_int r)

(* 
(* リストの要素の情報は捨てている *)
(* 結局、（途中のread_int()は関係無く）最初にqsを呼び出したときのnの値が返る *)
(* cmp: 比較関数
   n: リストの長さ *)
let rec qs (cmp : int -> int -> bool) n =
  if n <= 0 then
    0
  else
    let xs' = n - 1 in
    par cmp (read_int ()) 0 0 xs'

(* x: pivotの値
   xs: まだparしていない要素数
   l: 左にparした要素数
   r: 右にparした要素数
 *)
and  par (cmp : int -> int -> bool) x l r xs =
  if xs <= 0 then
    (* 全ての要素をparしたので、左右で再帰呼出し *)
    (* ここで1を足している *)
    qs cmp l + (1 + qs cmp r)
  else
    let x' = read_int () in
    let xs' = xs - 1 in
    if cmp x' x then
      par cmp x (1 + l) r xs'
    else
      par cmp x l (1 + r) xs'
  
let cmp (x : int) (y : int) = x >= y

let () =
  let n = read_int () in
  print_int @@ qs cmp n *)
