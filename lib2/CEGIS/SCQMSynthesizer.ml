open Core open Core.Poly
open Ast
open Ast.Logic

type papp = (Ident.pvar * Sort.t list) * (Term.t list)
type info = Previous of ((papp Set.Poly.t) * (papp Set.Poly.t)) list
type 'a result =
  | RSuccess of 'a
  | RRetry of info
  | RFail

type info_preds = (Ident.pvar * Sort.t list * bool) list

type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS
let ty_ex_info = TyEXPICS

(* temp *)

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

(*  type half_space = (Ident.tvar * Sort.t) list * Formula.t *)
type half_space = Formula.t
(*  type cover = half_space list *)
type edge = papp * papp

let is_divided_by ((pos, neg):edge) params (hs:half_space) =
  match is_included_in pos (params, hs), is_included_in neg (params, hs) with
  | true, false -> true
  | false, true -> true
  | _ -> false

let is_not_divided_by edge params (hs:half_space) =
  not @@ is_divided_by edge params hs

let gen_edges (pos:papp list)
    (neg:papp list) : edge list =
  List.fold_left pos ~init:[] ~f:(fun acc p ->
      List.fold_left neg ~init:acc ~f:(fun acc n -> (p, n)::acc)
    )


let assessment_of edges params (hs:half_space) =
  List.fold_left ~f:(fun acc edge ->
      if is_divided_by edge params hs then acc+1 else acc)
    ~init:0 edges

let the_best_hspace (hs:half_space list) params edges =
  let assessment_of hs = assessment_of edges params hs in
  let init = let hd = List.hd_exn hs in (hd, assessment_of hd) in
  let the_best, s = List.fold_left ~f:(fun (e, highscore) hspace ->
      let cur_score = assessment_of hspace in
      if cur_score > highscore
      then (hspace, cur_score)
      else (e, highscore)
    ) ~init:init hs in
  if s <= 0 then None else
    let remain_edges =
      List.filter edges ~f:(fun e -> is_not_divided_by e params the_best) in
    let remain_spaces =
      List.filter hs ~f:((<>) the_best) in
    Some (the_best, remain_edges, remain_spaces)

let reduce_spaces pos neg params (hs:half_space list) =
  let pos = Set.Poly.to_list pos in
  let neg = Set.Poly.to_list neg in
  let edges = gen_edges pos neg in
  let rec inner acc edges (hs:half_space list) =
    match edges with
    | [] -> Some(acc)
    | edges ->
      let open Util in
      the_best_hspace hs params edges >>= fun (best, edges, hspaces) ->
      inner (best::acc) edges hspaces
  in inner [] edges hs

let mk_vect params samples (hs:half_space list) =
  let bool_to_01 = function | true -> "1" | false -> "0" in
  List.fold_left ~f:(fun acc h ->
      acc ^ (bool_to_01 @@ is_included_in samples (params, h))
    ) ~init:"" hs

let gen_predicate pos neg params (hs:half_space list) =
  let pos = Set.Poly.to_list pos in
  let neg = Set.Poly.to_list neg in
  let open BooleanFunctionSynthesizer in
  Fptprover.Debug.print "call gen_predicate\n";
  if pos = [] then Formula.mk_atom (Atom.mk_false Dummy) Dummy
  else if neg = [] then Formula.mk_atom (Atom.mk_true Dummy) Dummy
  else
    begin
      let mk_vect = mk_vect params in
      let solver = gen_solver () in
      let solver = List.fold_left ~init:solver ~f:(fun acc p ->
          add_positive_s (mk_vect p hs) acc) pos in
      let solver = List.fold_left ~init:solver ~f:(fun acc n ->
          add_negative_s (mk_vect n hs) acc) neg in
      (*        Fptprover.Debug.print "call QM method\n"; *)
      let result = synthesize solver in
      (*        Fptprover.Debug.print "QM func return something\n"; *)
      let neg_op = fun x -> Formula.mk_neg x Dummy in
      let list_of_disj = filter_ neg_op hs result in
      List.map list_of_disj ~f:(fun conj -> Formula.and_of conj Dummy)
      |> fun ls -> Formula.or_of ls Dummy
    end

let mk_candidate (info: info) pos neg p
  : ((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) result =
  match p with
  | (pvar, sorts, true) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate (wf) for %s" id;
    gen_wf_predicate info pvar sorts pos neg
  | (pvar, sorts, false) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate for %s" id;
    let params, hs = Template.gen_half_spaces sorts pos in
    let hs = (Set.Poly.to_list hs) in (* TODO : use qual set if it is better than qual list *)
    Fptprover.Debug.print @@
    Printf.sprintf "half_spaces: %s" (Template.str_of_qualifiers hs);
    match reduce_spaces pos neg params hs with
    | Some (hs:half_space list) ->
      Fptprover.Debug.print @@
      Printf.sprintf "reduced half_spaces: %s"
        (Template.str_of_qualifiers hs);
      let candidate = gen_predicate pos neg params hs in
      (*       Some ((pvar, params), candidate) *)
      RSuccess ((pvar, params), candidate)
    | None -> RFail

let mk_candidates pinfo sample
  : ((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) list list=
  let open ExampleInstance in
  let map = mk_map_for_classification sample in
  let rec refine ((Previous info):info) =
    match classify info map sample with
    | None -> []
    | Some (positives, negatives) ->
      begin
        print_classified_examples positives negatives;
        let rec inner acc = function
          | [] -> [acc]
          | ((pvar, _, _) as p)::ps ->
            let positives, negatives =
              ExampleInstance.(sample_wrt_pred positives pvar,
                               sample_wrt_pred negatives pvar) in
            match mk_candidate (Previous info) positives negatives p with
            | RSuccess (target, phi) ->
              let candidate = target, (Logicutil.remove_dontcare phi) in
              inner (candidate::acc) ps
            | RRetry info -> refine info
            | RFail -> []
        in inner [] pinfo
      end
  in refine (Previous [])

let mk_candidates ex_info =
  let info_preds = match ex_info with EXPICS (x, _) -> x in
  mk_candidates info_preds
