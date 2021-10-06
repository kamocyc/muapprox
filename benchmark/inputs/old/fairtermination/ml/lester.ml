(* Taken from
   Lester, Neatherway, Ong, and Ramsay,
   "Model Checking Liveness Properties of Higher-Order Functional Programs",
   Appendix H.1
 *)

let event s = print_string s

let rec close1 flag i n y = event "Close1"; loop_after flag i n y
and loop flag i n y:unit =
  if flag then close1 flag i n y else loop_after flag i n y
and loop_after flag i n y = 
  if i<=n then loop flag (i+1) n y else y()

let g flag y n = loop flag 1 n y

let rec f x y n =
  if read_int () > 0 then
    f x y (n+1)
  else
    let flag = x() in
      g flag y n

let rec t():unit = event "Close2"; t()

let rec s() = event "Close1"; true

let main() =
    f s t 0

let () = main ()

(* base *)
(* Close2がいずれ起きる \/ Close1が起きない を表したい
後者の条件は、Close1が起きて、Close2が起きない場合は明らかにClose1が無限回起きるようにして表現している。
Globallyの条件は表現していない。
*)
(* The property checked in the original example is "AG (Close1 -> AF Close2)"
   In the program above, we have added a flag that expresses whether
   Close1 happened, so that 
   once Close1 occurs, it occurs infinitely often (unless Close2 occurs infinitely oftern)
 *)
(*{SPEC}
   fairness: (Always, Close1)  (* either Close1 happens only finitely often, or *)
   fairness: (Close2, Never) (* Close2 happens infinitely often *)
{SPEC}*)