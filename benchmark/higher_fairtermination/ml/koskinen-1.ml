(* Taken from 
   Koskinen and Terauchi, "Local Temporal Reasoning", CSL-LICS 2014, Figure 10 *)

let rec finish ():unit = print_string "Done";finish()
and reduce x r k =
   if x<=0 then k x else r x k
and explore x r =
(*  event "Explore"; *)
  reduce x r (fun y -> 
    if y<=0 then finish()
    else explore y r)

let f x k = k (x-2)

let main() =
  let t = Random.int(0) in
    explore t f

