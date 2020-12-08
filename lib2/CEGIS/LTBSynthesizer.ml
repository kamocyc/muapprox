open Core open Core.Poly
open Ast
open Ast.Logic

type info_preds = (Ident.pvar * Sort.t list * bool) list

type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS
let ty_ex_info = TyEXPICS

(* temp *)
type papp = (Ident.pvar * Sort.t list) * (Term.t list)
type info = Previous of ((papp Set.Poly.t) * (papp Set.Poly.t)) list
type 'a result =
  | RSuccess of 'a
  | RRetry of info
  | RFail

let str_of_info_preds pinfo =
  List.fold_left ~init:"" ~f:(fun acc (Ident.Pvar ident, _, is_wf) ->
      acc ^ "; " ^ ident ^ if is_wf then "is_wf" else "") pinfo

let is_included_in (_, terms) (params, phi) =
  let tvars, _ = List.unzip params in
  let map = List.zip_exn tvars terms |> Map.Poly.of_alist_exn in
  let phi = Formula.subst map phi in
  Logicutil.eval_formula phi

let set_param_range range phi =
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
  |> (fun phi -> Formula.and_of phi Dummy)
  |> (fun range_phi -> Formula.mk_and phi range_phi Dummy)

let gen_wf_predicate (info: info) pvar sorts pos neg =
  let params = Template.params_of_sorts sorts in
  let templ = Template.gen_linear_rf params in
  let pos' = pos |> Set.Poly.to_list |> List.map ~f:(fun p -> ExampleInstance.PApp p) in
  let neg' = neg |> Set.Poly.to_list |> List.map ~f:(fun p -> ExampleInstance.PApp p) in
  let phis = List.map pos' ~f:ExampleInstance.formula_of_example in
  let nphis = List.map neg' ~f:(fun n -> Formula.mk_neg (ExampleInstance.formula_of_example n) Dummy) in
  let _ = ignore nphis in
  let phi = Formula.and_of phis Dummy in
  let phi = Formula.subst_pred pvar params templ phi in
  Fptprover.Debug.print @@ "wf sat phi:"
                           ^ (Convert.PrinterHum.str_of_formula phi);
  let range = [1;2;4;8] in
  let rec refine level =
    match List.nth range level with
    | None ->
      let (Previous ls) = info in RRetry (Previous ((pos, neg)::ls))
    | Some range ->
      let phi' = set_param_range range phi in
      match Smt.Z3interface.check_satisfiability [phi'] with
      | None -> refine (level+1)
      | Some(model) ->
        let map = model in
        let zero = T_int.zero Dummy in
        let map' =
          List.map map ~f:(function
              | (tvar, None) -> (tvar, zero)
              | (tvar, Some(term)) -> (tvar, term))
          |> Map.Poly.of_alist_exn in
        RSuccess((pvar, params), Formula.subst map' templ)
  in refine 0

(* temp *)

let papps_to_exs ss = ss |> Set.Poly.to_list |> List.map ~f:(fun p -> ExampleInstance.PApp p)

let gen_coeff_constraint (pvar, params) templates pos neg =
  let pos', neg' = papps_to_exs pos, papps_to_exs neg in
  let phis, nphis =
    List.map pos' ~f:ExampleInstance.formula_of_example,
    List.map neg' ~f:(fun n -> Formula.mk_neg (ExampleInstance.formula_of_example n) Dummy) in
  Formula.mk_and (Formula.and_of phis Dummy)
    (Formula.and_of nphis Dummy) Dummy
  |> Formula.subst_pred pvar params templates

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
            |> List.map ~f:(fun (ident, sort) -> remove_dontcare_ ident sort)
            |> Map.Poly.of_alist_exn in
  Formula.subst var phi

let set_param_range range phi =
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
  |> (fun phi -> Formula.and_of phi Dummy)
  |> (fun range_phi -> Formula.mk_and phi range_phi Dummy)


let mk_pred template model =
  let map = model
            |> List.filter ~f:paramvar_filter
            |> List.map ~f:remove_dontcare
            |> Map.Poly.of_alist_exn in
  remove_paramvars (Formula.subst map template)

let mk_candidate (info: info) pos neg pinfo =
  match pinfo with
  | (pvar, sorts, true) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate (wf) for %s" id;
    gen_wf_predicate info pvar sorts pos neg
  | (pvar, sorts, false) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate for %s" id;
    let params = Template.params_of_sorts sorts in
    let (Previous ls) = info in
    let shape_range = [(1, 1); (1, 2); (2, 1); (2, 2)] in
    let param_range = [1; 2; 4; 8; 16] in
    let rec refine_shape slevel =
      let rec refine_param template plevel phi =
        match List.nth param_range plevel with
        | None -> refine_shape (slevel+1)
        | Some prange ->
          let phi' = set_param_range prange phi in
          match Smt.Z3interface.check_satisfiability [phi'] with
          | None -> refine_param template (plevel + 1) phi
          | Some model ->
            RSuccess ((pvar, params), mk_pred template model)
      in
      match List.nth shape_range slevel with
      | None -> RRetry (Previous ((pos, neg)::ls))
      | Some (conj, disj) ->
        let template = Template.gen_dnf_template params conj disj in
        let phi' = gen_coeff_constraint (pvar, params) template pos neg in
        refine_param template 0 phi'
    in refine_shape 0

let mk_candidates (info_preds: info_preds) (sample: ExampleInstance.t)
  : ((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) list list =
  let open ExampleInstance in
  let map = mk_map_for_classification sample in
  let rec refine ((Previous info):info) =
    let open Util in
    classify info map sample >>= fun (positives, negatives) ->
    print_classified_examples positives negatives;
    let rec inner acc = function
      | [] -> Some(acc)
      | ((pvar, _, _) as p)::ps ->
        let positives, negatives =
          ExampleInstance.(sample_wrt_pred positives pvar,
                           sample_wrt_pred negatives pvar) in
        match mk_candidate (Previous info) positives negatives p with
        | RSuccess (target, phi) ->
          let candidate = target, (Logicutil.remove_dontcare phi) in
          inner (candidate::acc) ps
        | RRetry info -> refine info
        | RFail -> None
    in inner [] info_preds
  in
  match refine (Previous []) with
  | None -> []
  | Some x -> [x]

let mk_candidates ex_info =
  let info_preds = match ex_info with EXPICS (x, _) -> x in
  mk_candidates info_preds
