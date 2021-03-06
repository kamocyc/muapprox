let rec sum n =
  if n = 0 then 0
  else n + sum (n-1)

let main' () =
  let n = read_int () in
  sum n

let main () =
  assert (main' () = 0)
(*

%HES
MAIN_232  =v
  Exists
   (\arg1_251.
     SUM arg1_251 (\x_246.(arg1_251 > x_246 \/ false) /\ (arg1_251 <= x_246 \/ FAIL_239 true (\main_243.false)))).
FAIL_239 u_240 k_241 =v false.
SUM n_2 k_sum_17 =v (n_2 > 0 \/ k_sum_17 0) /\ (n_2 <= 0 \/ SUM (n_2 - 1) (\x_254.k_sum_17 (n_2 + x_254))).
Forall p      =v ∀n. p n.
Exists p        =v ExistsAux 1000 0 p.
ExistsAux x p =v x > 0 /\ (p x \/ p (0-x) \/ ExistsAux (x-1) p).

*)
