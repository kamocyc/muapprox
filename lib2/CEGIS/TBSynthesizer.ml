open Core open Core.Poly
open Ast
open Ast.Logic

type info_preds = (Ident.pvar * Sort.t list * bool) list

type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS

let gen_coeff_constraint templates (sample:ExampleInstance.t) =
  let phi = ExampleInstance.formula_of sample in
  List.fold_left ~f:(fun acc ((pvar, params), phi') ->
      Formula.subst_pred pvar params phi' acc
    ) ~init:phi templates

let paramvar_filter (Ident.Tvar ident, _) =
  String.substr_index ~pattern:"paramvar" ident <> None

let remove_dontcare (tvar, v) =
  let zero = T_int.zero Dummy in (* TODO: extend to real *)
  match v with
  | None -> (tvar, zero)
  | Some (term) -> (tvar, term)

let remove_dontcare_ ident sort =
  match sort with
  | T_int.SInt -> (ident, T_int.zero Dummy)
  | T_int.SReal -> (ident, T_int.mk_real "0" Dummy)
  | _ -> assert false

let remove_paramvars (phi:Formula.t) =
  let open Ast.Gather in
  let var = free_variables_of_formula phi
            |> Variables.to_list
            |> List.filter ~f:paramvar_filter
            |> List.map ~f:(fun (ident, sort)
                             -> remove_dontcare_ ident sort)
            |> Map.Poly.of_alist_exn in
  Formula.subst var phi

let make_candidates templates model =
  (* TODO: refactoring *)
  let map = model
            |> List.filter ~f:paramvar_filter
            |> List.map ~f:remove_dontcare
            |> Map.Poly.of_alist_exn in
  List.map templates ~f:(fun ((pvar, params), phi) ->
      ((pvar, params), Formula.subst map phi))
  |> List.map ~f:(fun (target, phi) ->
      (target, remove_paramvars phi))

let gen_templates (info_preds:info_preds) =
  let open Fptprover in
  let config = !Global.config in
  List.map info_preds ~f:(fun (pvar, sorts, is_wf) ->
      let params = Template.params_of_sorts sorts in
      ((pvar, params),
       if is_wf then Template.gen_linear_rf params
       else Template.gen_dnf_template params
           (config.number_of_conj)
           (config.number_of_disj)
      ))

let set_param_range level phi =
  let param_range = if !Fptprover.Global.config.coeff_restriction then !Fptprover.Global.config.coeff_restriction_strategy else [] in
  match List.nth param_range level with
  | None ->
    (*Fptprover.Debug.print @@ "infinity!";*)
    None
  | Some range ->
    (*Fptprover.Debug.print @@ (string_of_int range) ^ "!";*)
    let open Gather in
    let geq_ t = Formula.mk_atom
        (T_int.mk_geq t (T_int.mk_from_int (-range) Dummy) Dummy)
        Dummy in
    let leq_ t = Formula.mk_atom
        (T_int.mk_leq t (T_int.mk_from_int range Dummy) Dummy)
        Dummy in
    let range_ t = Formula.mk_and (geq_ t) (leq_ t) Dummy in
    let free_vars = free_variables_of_formula phi |> Variables.to_list in
    List.map free_vars ~f:(fun (ident, sort) ->
        range_ (Term.mk_var ident sort Dummy))
    |> (fun phis -> Formula.and_of phis Dummy)
    |> (fun range_phi -> Some (Formula.mk_and phi range_phi Dummy))

let rec mk_candidates (info_preds:info_preds) (sample:ExampleInstance.t)
  : (((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) list) list =
  let templates = gen_templates info_preds in
  let phi = gen_coeff_constraint templates sample in
  let rec inner level =
    match set_param_range level phi with
    | None -> Smt.Z3interface.check_satisfiability [phi]
    | Some phi' ->
      (match Smt.Z3interface.check_satisfiability [phi'] with
       | None -> inner (level + 1)
       | x -> x)
  in (* refine templates *)
  match inner 0 with
  | Some model -> [make_candidates templates model]
  | None ->
    let config = !Fptprover.Global.config in
    (*Fptprover.Debug.print @@ (string_of_int (config.number_of_conj)) ^ "*" ^ (string_of_int (config.number_of_disj));*)
    let nc', nd' =
      if (config.number_of_conj + config.number_of_disj) mod 2 = 0 then
        config.number_of_conj + 1, config.number_of_disj
      else
        config.number_of_conj, config.number_of_disj + 1
    in
    Fptprover.Global.config := !Fptprover.Global.config
                               |> Config.update_number_of_conj nc'
                               |> Config.update_number_of_disj nd';
    mk_candidates info_preds sample

let mk_candidates ex_info =
  let info_preds = match ex_info with
    | EXPICS (x, _) -> x in
  mk_candidates info_preds

let ty_ex_info = TyEXPICS
