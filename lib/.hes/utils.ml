open Ast.Logic
open Hes

let rec replace_app (replacer: Formula.t -> Formula.t) formula =
  if Formula.is_atom formula then
    let atom, info = Formula.let_atom formula in
    let formula = Formula.mk_atom atom info in
    if Atom.is_app atom then
      let pred, _, _ = Atom.let_app atom in
      if Predicate.is_var pred then
        replacer formula
      else formula
    else
      formula
  else if Formula.is_binop formula then
    let binop, left, right, info = Formula.let_binop formula in
    Formula.mk_binop binop (replace_app replacer left) (replace_app replacer right) info
  else if Formula.is_unop formula then
    let unop, body, info = Formula.let_unop formula in
    Formula.mk_unop unop (replace_app replacer body) info
  else if Formula.is_bind formula then
    let binder, bounds, body, info = Formula.let_bind formula in
    Formula.mk_bind binder bounds (replace_app replacer body) info
  else assert false

let replace_app_add formula arg sort =
  replace_app (fun fml ->
      let atom, info = Formula.let_atom fml in
      let pred, args, info' = Atom.let_app atom in
      let pvar, arg_sorts = Predicate.let_var pred in
      Formula.mk_atom
        (Atom.mk_app
           (Predicate.mk_var pvar (sort :: arg_sorts))
           (arg :: args)
           info'
        ) info
    ) formula

let elim_mu_from_funcs_with_rec funcs tvar_rec =
  List.map (fun func ->
      let fix, pvar, args, body = (HesLogic.let_function func) in
      let args = (tvar_rec, T_int.SInt) :: args in
      let term = Term.mk_var tvar_rec T_int.SInt Dummy in
      if fix = Predicate.Nu then
        let body = replace_app_add body term T_int.SInt in
        HesLogic.mk_func Predicate.Nu pvar args body
      else
        (* replace all F X Y --> F (rec_ - 1) X Y in body*)
        let term = Term.mk_funapp T_int.Sub [term; T_int.mk_int 1 Dummy] Dummy in
        let body = replace_app_add body term T_int.SInt in
        (* body --> rec_ > 0 /\ body *)
        let body = Formula.mk_and
            (Formula.mk_atom
               (T_int.mk_gt term (T_int.mk_int 0 Dummy) Dummy)
               Dummy)
            body Dummy in
        HesLogic.mk_func Predicate.Nu pvar args body
    ) funcs
