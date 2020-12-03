let mult' k =
  let rec mult m n (k : int -> unit) : unit =
    if m > 0 then
      mult (m - 1) n (fun r -> k (r + n))
    else
      k 0
  in
    let m = read_int () in
    let n = read_int () in
    if m > 0 then mult m n k else k 0

let () =
  mult' (fun r -> print_int r)

(* 

Main =v Mult_in (\r. true).
Mult_in k =v ∀m. ∀n. (m > 0 => Mult m n k) /\ (m <= 0 => k 0).
Mult m n k =u (m > 0 => Mult (m - 1) n (\r. k (r + n))) /\ (m <= 0 => k 0).

 *)