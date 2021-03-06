let rec f n k =
  let r = read_int () in
  let delta = if r > 0 then r else 1-r in
  let n_next = n - delta in
  if n_next > 0 then
    f n_next k
  else
    k ()

let () =
  f (read_int ()) (fun r -> r)

(*

Main =v ∀n. F n (\r. true).
F n k =u ∀r. ((r > 0 => F1 (n - r) k) /\ (r <= 0 => F1 (n - (1 - r)) k).
F1 n_next k =u (n_next > 0 => F n_next k) /\ (n_next <=0 => k true).
*)