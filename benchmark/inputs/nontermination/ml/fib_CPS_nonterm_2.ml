(*
Sentry =v Main true (\r. false).
Main u c =v ∃r. Fib r Id c.
Id n c =v c n.
Cont2 a k b c =v k (a + b) c.
Cont1 ppn k a c =v Fib ppn (Cont2 a k) c.
Fib n k c =v
  ((n = 0 \/ n = 1) => k 1 c) /\
  ((n != 0 /\ n != 1) => Fib (n - 1) (Cont1 (n - 2) k) c).
 *)
let rec fib_CPS_nonterm n k c =
  if n = 0 || n = 1 then k 1 c
  else
    let pn = n - 1 in
    let ppn = n - 2 in
    fib_CPS_nonterm pn (cont1 ppn k) c
and cont1 ppn k a c = fib_CPS_nonterm ppn (cont2 a k) c
and cont2 a k b c = k (a + b) c
let id (n:int) c = c n
let main () c =
  let r = read_int () in
  fib_CPS_nonterm r id c

let () = main () (fun r -> print_int r)


