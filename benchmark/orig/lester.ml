(* Taken from
   Lester, Neatherway, Ong, and Ramsay,
   "Model Checking Liveness Properties of Higher-Order Functional Programs",
   Appendix H.1
 *)


let rec loop flag i n y:unit =
  (if flag then event "Close1" else ());
  if i<=n then loop flag (i+1) n y else y()

let g flag y n = loop flag 1 n y

let rec f x y n =
  if Random.int 0>0 then
     f x y (n+1)
  else
     let flag = x() in
       g flag y n

let rec t():unit = event "Close2"; t()

let rec s() = event "Close1"; true

let main() =
     f s t 0

(* The property checked in the original example is "AG (Close1 -> AF Close2)"
   In the program above, we have added a flag that expresses whether
   Close1 happened, so that 
   once Close1 occurs, it occurs infinitely often
 *)
(*{SPEC}
   fairness: (Call, Close1)  (* either Close1 happens only finitely often, or *)
   fairness: (Close2, Never) (* Close2 happens infinitely often *)
{SPEC}*)