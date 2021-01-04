open Ast.Logic

let rec remove_unused_bounds fml =
  if Formula.is_atom fml then
    fml (* TODO *)
  else if Formula.is_and fml then
    let fml1, fml2, info = Formula.let_and fml in
    Formula.mk_and
      (remove_unused_bounds fml1)
      (remove_unused_bounds fml2)
      info
  else if Formula.is_or fml then
    let fml1, fml2, info = Formula.let_or fml in
    Formula.mk_or
      (remove_unused_bounds fml1)
      (remove_unused_bounds fml2)
      info
  else if Formula.is_bind fml then
    let binder, bounds, fml, info = Formula.let_bind fml in
    let fml = remove_unused_bounds fml in
    let ftv = Formula.get_ftv fml in
    let bounds = List.filter (fun (tvar, _) -> Core.Set.Poly.mem ftv tvar) bounds in
    Formula.mk_bind_if_bounded binder bounds fml info
  else if Formula.is_neg fml then
    let fml, info = Formula.let_neg fml in
    Formula.mk_neg
      (remove_unused_bounds fml)
      info
  else
    failwith "not implemented"

let optimize fml =
  fml
  |> remove_unused_bounds
