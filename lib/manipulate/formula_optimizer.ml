open Hflmc2_syntax

let remove_unused_bounds (phi : 'a Hflz.t) =
  let is_used x phi =
    IdSet.exists (Hflz.fvs phi) ~f:(Id.eq x) in
  let rec go (phi_ : 'a Hflz.t) = match phi_ with
    | Bool _ | Var _ | Arith _ | Pred _ -> phi
    | Or (phi1, phi2)  -> Or  (go phi1, go phi2)
    | And (phi1, phi2) -> And (go phi1, go phi2)
    | App (phi1, phi2) -> And (go phi1, go phi2)
    | Abs (x, phi1) ->
      let phi1 = go phi1 in
      if is_used x phi1 then Abs (x, phi1) else phi1
    | Forall (x, phi1) ->
      let phi1 = go phi1 in
      if is_used x phi1 then Forall (x, phi1) else phi1
    | Exists (x, phi1) ->
      let phi1 = go phi1 in
      if is_used x phi1 then Exists (x, phi1) else phi1 in
  go phi

let optimize fml =
  fml
  |> remove_unused_bounds
