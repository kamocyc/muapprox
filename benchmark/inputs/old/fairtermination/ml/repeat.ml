
let rec repeat g =
  g (read_int ())
and eventA () = print_endline "A"; repeat f
and f x =
  if x>0 then f (x-1) else eventA ()
let main = repeat f

(* repeat -> (f->)* -> eventA -> repeat -> ... *)
(* 
(* CPS *)
let a k = k ()

let rec repeat g k =
  g (Random.int 0) (fun _ -> 
  repeat g k)

(* Aが *)
let rec f x k =
  if x>0 then f (x-1) k else a k
let main = repeat f (fun _ -> ())
 *)

(* 
let event a = ()

let rec repeat g =
  g (Random.int 0);
  repeat g

(* Aが *)
let rec f x =
  if x>0 then f (x-1) else event "A"
let main = repeat f *)

(* 
f xの呼び出し回数が異なるだけであり、Aは書くrepeat gごとに1回だけ呼ばれる

repeat f
->
f (rand())
->(x > 0)
f x -> ()* ->[0回以上]) event "A"
->
repeat f



 *)
