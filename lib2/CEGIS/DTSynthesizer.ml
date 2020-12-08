open Core open Core.Poly
open Ast
open Ast.Logic

type papp = (Ident.pvar * Sort.t list) * (Term.t list)
type info = Previous of ((papp Set.Poly.t) * (papp Set.Poly.t)) list
type 'a result =
  | RSuccess of 'a
  | RRetry of info
  | RFail

type info_preds = (Ident.pvar *  Sort.t list * bool) list

type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS
let ty_ex_info = TyEXPICS

(* temp *)

let str_of_info_preds pinfo =
  List.fold_left ~init:"" ~f:(fun acc (Ident.Pvar ident, _, is_wf) ->
      acc ^ "; " ^ ident ^ if is_wf then "is_wf" else "") pinfo

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

type dtree = Leaf of bool | Node of Formula.t * dtree * dtree
type qual = (Ident.tvar * Sort.t) list * Formula.t
type edge = papp * papp

let is_included_in (_, terms) (params, phi) =
  let tvars, _ = List.unzip params in
  let map = List.zip_exn tvars terms |> Map.Poly.of_alist_exn in
  let phi = Formula.subst map phi in
  Logicutil.eval_formula phi

let rec formula_of_tree = function
  | Leaf b -> Formula.mk_atom (
      if b then Atom.mk_true Dummy
      else Atom.mk_false Dummy) Dummy
  | Node (q, t1, t2) ->
    let temp1 = Formula.mk_and q (formula_of_tree t1) Dummy in
    let temp2 =
      Formula.mk_and (Formula.mk_neg q Dummy) (formula_of_tree t2) Dummy in
    Formula.mk_or temp1 temp2 Dummy

(* TODO: merge into is_included for geo *)
(*  let is_included_in (_, terms)
                     ((params, phi): qual) =
    let tvars, _ = List.unzip params in
    let map = List.zip_exn tvars terms in
    let phi = Formula.subst map phi in
    Logicutil.eval_formula phi *)

let gen_edges (pos:papp Set.Poly.t)
    (neg:papp Set.Poly.t) : edge Set.Poly.t =
  Set.Poly.fold pos ~init:Set.Poly.empty ~f:(fun acc p ->
      Set.Poly.fold neg ~init:acc ~f:(fun acc n -> Set.Poly.add acc (p, n))
    )

let divide qual examples =
  Set.Poly.partition_tf ~f:(fun ex -> is_included_in ex qual) examples

let is_divided_by ((pos, neg):edge) (hs:qual) =
  match is_included_in pos hs, is_included_in neg hs with
  | true, false -> true
  | false, true -> true
  | _ -> false

let is_not_divided_by edge (hs:qual) =
  not @@ is_divided_by edge hs

let entropy (p, n) =
  let open Util in
  let p, n = float_of_int (Set.Poly.length p),
             float_of_int (Set.Poly.length n) in
  let l = if p > 0. then
      (p /. (p +. n)) *. log2 (p /. (p +. n))
    else 0. in
  let r = if n > 0. then
      (n /. (p +. n)) *. log2 (n /. (p +. n))
    else 0. in
  let res = (-1.) *. (l +. r) in
  assert (res >= 0. && res <= 1.);
  res

let divide q (p, n) =
  let qp, nqp = divide q p in
  let qn, nqn = divide q n in
  (qp, qn), (nqp, nqn)

let assessment_of (edges:edge Set.Poly.t) (hs:qual) =
  Set.Poly.fold ~f:(fun acc edge ->
      if is_divided_by edge hs then acc+1 else acc)
    ~init:0 edges

let the_best_hspace (hs:qual Set.Poly.t) (edges:edge Set.Poly.t) =
  let assessment_of hs = assessment_of edges hs in
  let init = match Set.Poly.choose hs with
    | Some hd -> (hd, assessment_of hd)
    | None -> failwith "hs must contain at least one element"
  in
  let the_best, s = Set.Poly.fold ~f:(fun (e, highscore) hspace ->
      let cur_score = assessment_of hspace in
      if cur_score > highscore
      then (hspace, cur_score)
      else (e, highscore)
    ) ~init:init hs in
  if s <= 0 then None else
    let remain_edges =
      Set.Poly.filter edges ~f:(fun e -> is_not_divided_by e the_best) in
    let remain_spaces =
      Set.Poly.filter hs ~f:((<>) the_best) in
    Some (the_best, remain_edges, remain_spaces)

let reduce_spaces pos neg (hs:qual Set.Poly.t) =
  let edges = gen_edges pos neg in
  let rec inner acc edges (hs:qual Set.Poly.t) =
    if Set.Poly.is_empty edges then Some(acc) else
      let open Util in
      the_best_hspace hs edges >>= fun (best, edges, hspaces) ->
      inner (Set.Poly.add acc best) edges hspaces
  in inner Set.Poly.empty edges hs

let choose_qualifier (quals:qual Set.Poly.t) pos neg : qual option =
  if Set.Poly.is_empty quals then None
  else
    begin
      let gain q =
        let len_d (p, n) = float_of_int(Set.Poly.length p + Set.Poly.length n) in
        let d = (pos, neg) in
        let d_q, d_nq = divide q d in
        entropy d -.
        ((len_d d_q *. entropy d_q) +. (len_d d_nq *. entropy d_nq)) in
      match Set.Poly.choose quals with
      | None -> failwith "quals must contains at least one element"
      | Some hd ->
        let init = (hd, gain hd) in
        let q, _ =
          Set.Poly.fold
            ~init:init
            ~f:(fun (q, ig) q' ->
                let ig' = gain q' in
                if ig' > ig then (q', ig') else (q, ig)) quals
        in Some q
    end

let rec build_tree (quals:qual Set.Poly.t) (pos, neg) =
  if Set.Poly.is_empty neg then Leaf true
  else if Set.Poly.is_empty pos then Leaf false
  else
    match choose_qualifier quals pos neg with
    | None -> failwith "lack of qualifiers"
    | Some((_, q) as qual)->
      let d_q, d_nq = divide qual (pos, neg) in
      let quals = Set.Poly.remove quals qual in
      Node (q, build_tree quals d_q, build_tree quals d_nq)

let mk_candidate with_reduction default_quals (info: info) pos neg pinfo
  : ((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) result =
  match pinfo with
  | (pvar, sorts, true) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate (wf) for %s" id;
    gen_wf_predicate info pvar sorts pos neg
  | (pvar, sorts, false) ->
    let Ident.Pvar id = pvar in
    Fptprover.Debug.print @@ Printf.sprintf "mk_candidate for %s" id;
    let params, quals = Template.gen_half_spaces sorts (Set.Poly.union pos neg)  in
    let quals = Set.Poly.union default_quals quals in
    let quals_num = Set.Poly.length quals in
    Fptprover.Debug.print @@
    Printf.sprintf "qualifiers: %s" (Template.str_of_qualifiers @@ Set.Poly.to_list quals); (* TODO : to_list is required by only debug mode *)
    let quals = Set.Poly.map ~f:(fun q -> params, q) quals in
    try
      let quals =
        if with_reduction then
          match reduce_spaces pos neg quals with
          | None -> raise (Not_found_s (List []))
          | Some quals ->
            quals
            |> Set.Poly.map ~f:snd
            |> Set.Poly.to_list (* TODO : print quals as a Set *)
            |> Template.str_of_qualifiers
            |> fun qual_text ->
            Printf.sprintf "reduced half_spaces: %s\n (%d -> %d)"
              qual_text quals_num (Set.Poly.length quals)
            |> Fptprover.Debug.print;
            quals
        else quals
      in
      let d = (pos, neg) in
      RSuccess ((pvar, params), (formula_of_tree (build_tree quals d)))
    with Not_found_s _ -> RFail

let mk_candidates default_quals_map pinfo sample
  : ((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) list list =
  let open ExampleInstance in
  let config = !Fptprover.Global.config in
  let mk_candidate = mk_candidate config.dt_reduction in
  let map = mk_map_for_classification sample in
  let rec refine ((Previous info):info) =
    match classify info map sample with
    | None -> []
    | Some (positives, negatives) ->
      print_classified_examples positives negatives;
      let rec inner acc = function
        | [] -> [acc]
        | ((pvar, _, _) as p)::ps ->
          let default_quals =
            match List.Assoc.find default_quals_map ~equal:(=) pvar with
            | None -> Set.Poly.empty
            | Some q -> q
          in
          let positives, negatives =
            ExampleInstance.(sample_wrt_pred positives pvar,
                             sample_wrt_pred negatives pvar) in
          match mk_candidate default_quals (Previous info) positives negatives p with
          | RSuccess (target, phi) ->
            let candidate = target, (Logicutil.remove_dontcare phi) in
            inner (candidate::acc) ps
          | RRetry info -> refine info
          | RFail -> []
      in inner [] pinfo
  in refine (Previous [])

let mk_candidates ex_info =
  let info_preds, quals =
    match ex_info with
    | EXPICS (x, cs) ->
      let config = !Fptprover.Global.config in
      let default_quals = if config.default_qualifier then Template.get_default_qualifiers cs else [] in
      x, default_quals
  in
  mk_candidates quals info_preds
