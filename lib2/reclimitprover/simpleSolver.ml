open Ast
open Logic
open Convert
open Fptprover
open Hes

(* tvar > -coe * a - coe * b + coe /\ tvar > -coe * a + coe * b + coe /\ tvar > coe * a - coe * b + coe /\ tvar > coe * a + coe * b + coe *)
let rec mk_havoc_rep args tvar coe term = match args with
  | [] -> Formula.mk_atom (T_int.mk_gt tvar term Dummy) Dummy
  | (arg_tvar, arg_sort) :: tail ->
    let arg = Term.mk_var arg_tvar arg_sort Dummy in
    (Formula.mk_and
       (mk_havoc_rep tail tvar coe (T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int (-coe) Dummy) arg Dummy) Dummy))
       (mk_havoc_rep tail tvar coe (T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int coe Dummy) arg Dummy) Dummy))
       Dummy)

let mk_havoc args tvar coe = mk_havoc_rep args tvar coe (T_int.mk_from_int coe Dummy)

let solve_onlyforall_with_coe timeout coe hes =
  let approx_result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout true @@ Hesutil.get_greatest_approx_hes hes in
  if approx_result = Status.Invalid then
    Status.Invalid
  else
    let tvar_rec = Ident.Tvar "rec_" in
    let funcs = Hesutil.elim_mu_from_funcs_with_rec (HesLogic.get_functions hes) tvar_rec in
    let term_rec = Term.mk_var tvar_rec T_int.SInt Dummy in
    let entry = Hesutil.replace_app_add (HesLogic.get_entrypoint hes) term_rec T_int.SInt in
    let entry =
      if Formula.is_forall entry then
        let bounds, body, info = Formula.let_forall entry in
        Formula.mk_forall ((tvar_rec, T_int.SInt) :: bounds)
          (Formula.mk_imply
             (mk_havoc bounds term_rec coe)
             body
             Dummy) info
      else
        Formula.mk_forall
          [tvar_rec, T_int.SInt]
          (Formula.mk_imply (mk_havoc [] term_rec coe) entry Dummy)
          Dummy
    in
    let hes = HesLogic.mk_hes funcs entry in
    Debug.print @@ Printf.sprintf "Converted Hes: %s\n" @@ Hesutil.str_of_hes hes;
    let result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout true hes in
    if result = Status.Valid then
      Status.Valid
    else
      Status.Unknown

let solve_onlyforall timeout hes =
  solve_onlyforall_with_coe timeout 10 hes

let solve_onlyexists _ _ =
  Printf.printf "not implemented\n";
  assert false

let solve hes =
  let timeout = 10 in
  if Hesutil.is_onlyforall hes && HesLogic.is_onlynu hes then
    let result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout true hes in
    result
  else if Hesutil.is_onlyexists hes && HesLogic.is_onlymu hes then
    let result, _ = Rfunprover.Solver.solve_onlymu_onlyexists false timeout true hes in
    result
  else if Hesutil.is_onlyforall hes then
    solve_onlyforall timeout hes
  else if Hesutil.is_onlyexists hes then
    solve_onlyexists timeout hes
  else
    (Printf.printf "not implemented\n";
     assert false)

let solve_formula fml =
  Debug.print @@ Printf.sprintf "Input Formula: %s" @@ PrinterHum.str_of_formula fml;
  let fml = Ast.Logic.Formula.simplify @@ FormulaConverter.elim_fv_with_forall fml in
  Debug.print @@ Printf.sprintf "Input Formula: %s" @@ PrinterHum.str_of_formula fml;
  let hes = Hesutil.hes_of_formula fml in
  Debug.print @@ Printf.sprintf "Input Hes: %s" @@ Hesutil.str_of_hes hes;
  solve hes
