(*
USED: PEPM2013 as forall_eq_pair
*)

let rec for_all f (xs:(int*int) list) =
  match xs with
      [] -> true
    | x::xs' ->
        f x && for_all f xs'

let rec eq_pair ((x:int),(y:int)) = x = y

let rec make_list n =
  if n < 0
  then []
  else (n,n) :: make_list (n-1)

let main n = assert (for_all eq_pair (make_list n))
