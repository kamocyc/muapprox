open Core
open Convert
open Fptprover
open Ast
open Ast.Logic

let select_synthesizer =
  let open Synthesizer in
  function
  | Config.TBSynth ->
    let module Synth = Validator.Make(TBSynthesizer) in Synth.solve
  | Config.SCQMSynth ->
    let module Synth = Validator.Make(SCQMSynthesizer) in Synth.solve
  | Config.DTSynth ->
    let module Synth = Validator.Make(DTSynthesizer) in Synth.solve
  | Config.LTBSynth ->
    let module Synth = Validator.Make(LTBSynthesizer) in Synth.solve
  | Config.PASIDSynth ->
    let module Synth = Validator.Make(PASIDSynthesizer) in Synth.solve
  | Config.PASATSynth ->
    let module Synth = Validator.Make(PASATSynthesizer) in Synth.solve
  | Config.TB_DTSynth ->
    let module Synth = Validator.Make(TB_DT_Synthesizer) in Synth.solve
  | Config.TB_DT_PASATSynth ->
    let module Synth = Validator.Make(TB_DT_PASATSynthesizer) in Synth.solve

let print_hr ()=
  Debug.print "==========================================================="

let print_psat_problem phis cs = 
  Debug.print @@
    ("original problem:" ^ (List.fold_left ~init:"" 
                              ~f:(fun acc phi -> acc ^ "\n" 
                                                 ^ (PrinterHum.str_of_formula phi)) phis))
    ^ "\nconstraints: " ^ (Constraint.string_of_constraints cs)

let print_iteration ct samples=
  Debug.print "-----------------------------------------";
  Debug.print @@ "iteration : " ^ (string_of_int ct);ignore(samples)

let print_candidates candidates =
  Debug.print @@
  "predicate assignments candidates : " ^ (PrinterHum.str_of_candidates candidates)

let print_info_for_predicates label phis =
  let num_of_pvars = Formula.get_fpv (Formula.and_of phis Dummy) |> Set.Poly.length in
  let num_of_constraints = List.length phis in
  Debug.print label;
  Debug.print @@
    Printf.sprintf 
      "number of predicate variables: %d, number of constraints: %d\n" num_of_pvars num_of_constraints

let prove synth_predicates phi =
  Debug.print @@ "******* parsed formula: " ^ (PrinterHum.str_of_formula phi) ^ "\n";
  let desugared_phi = Desugar.of_formula phi in
(*  let renamed_phi = Formula.refresh_pvar desugared_phi in *)
  let renamed_phi = Formula.refresh_tvar desugared_phi in
  let hes = Convert.Hesutil.hes_of_formula renamed_phi in
  Debug.print @@ "******* hes: " ^ (Convert.Hesutil.str_of_hes hes) ^ "\n";
  let constraints = Constraint.extract hes in
  Debug.print @@ "******* generated pCSP: " ^ (Constraint.string_of_constraints constraints) ^ "\n";
  match synth_predicates constraints with
  | (Some _), _ -> Status.Valid
  | None, _ -> Status.Unknown (*failwith "Every synthesizer must generate predicate candidates for any inputs."*)

let predicate_sat synth_predicates cs =
  match synth_predicates cs with
  | Some _ -> Status.Valid
  | None -> Status.Invalid

let formula_for_disprove phi =
  let open Gather in
  let free_vars = free_variables_of_formula phi |> Variables.to_list in 
  let phi = Formula.mk_forall free_vars phi Dummy in
  Formula.mk_neg phi Dummy

let valid_to_invalid = function
  | Status.Invalid -> Status.Valid
  | Status.Valid   -> Status.Invalid
  | x -> x

let check_validity_of_fixpoint_formula phi =
  Debug.print "======== Solving by CEGISprover ========";
  let config = !Global.config in
  let solve = select_synthesizer (config.synthesizer) in
  let prove = prove solve in
  let prove phi = match prove phi with
    | Status.Valid -> Status.Valid | Status.Unknown -> Status.Unknown | _ -> failwith "Invalid output" in
  let disprove phi = match prove (formula_for_disprove phi) with
    | Status.Valid -> Status.Invalid | Status.Unknown -> Status.Unknown | _ -> failwith "Invalid output" in
  let result = match config.mode with
    | Config.Prove ->
       Debug.print "-=-=-=-= proving -=-=-=-=";
       prove phi |> (function Status.Unknown -> disprove phi | x -> x)
    | Config.Disprove ->
       Debug.print "-=-=-=-= disproving -=-=-=-=";
       disprove phi |> (function Status.Unknown -> prove phi | x -> x)
    | Config.Parallel -> failwith "parallel mode is not implemented."
  in
  Debug.print "===================================================================";
  result

let complete_solution phis sol =
  Debug.print "\n**** complete solutions ****\n";
  let nnf_of_phis =
    phis
    |> List.rev_map ~f:Desugar.of_formula
    |> List.rev_map ~f:Logicutil.nnf_of
  in
  let const_predicates = Preprocessor.const_predicates nnf_of_phis in
  let sol = const_predicates @ sol in
  let sol_map =
        sol
        |> List.map ~f:(fun ((pvar, params), formula) -> pvar, (params, formula))
        |> Map.Poly.of_alist_exn
  in
  let phis' = List.map ~f:(Formula.subst_preds sol_map) phis in
  Debug.print "Substitute Solutions into the origianl Formula : [";
  List.iter ~f:(fun phi -> Debug.print @@ Convert.PrinterHum.str_of_formula phi) phis';
  Debug.print "]\n";

  let phis' = List.filter_map
        ~f:(fun phi -> if List.length @@ Formula.count_pvar_apps phi = 0 then None else Some phi) phis' in
  let sol =
    if List.length phis' = 0
    then sol (* There is no non-rec predicate *)
    else
      let sol' =
          phis'
          |> List.rev_map ~f:Desugar.of_formula
          |> List.rev_map ~f:Logicutil.nnf_of
          |> List.rev_map ~f:(fun phi -> Formula.cnf_of phi)
          |> List.concat
          |> List.filter ~f:(fun (ps, ns, _) -> List.length ps + List.length ns > 0)
          |> fun cnf -> if List.length cnf = 0 then [] else Preprocessor.solve_non_rec cnf
      in
      sol' @ sol
  in
  sol

let check_ans phis sol =
  let sol_map =
        sol
        |> List.map ~f:(fun ((pvar, params), formula) -> pvar, (params, formula))
        |> Map.Poly.of_alist_exn
  in
  let phis = List.map ~f:(Formula.subst_preds sol_map) phis in
  let result = List.fold_left ~init:true phis
    ~f:(fun acc phi -> 
      match Smt.Z3interface.check_validity phi with
      | None -> acc
      | Some _ -> false
    ) in
  Debug.print @@ "check result with Z3 : " ^ if result then "correct" else "wrong"

let solve_pcsp phis =
  let config = !Global.config in
  let synth_predicates = select_synthesizer (config.synthesizer) in
  phis
  |> ((*print_endline "Desugar@solve_psat";*) List.rev_map ~f:Desugar.of_formula)
  |> ((*print_endline "nnf_of@solve_psat" ;*) List.rev_map ~f:Logicutil.nnf_of)
  |> (fun phis -> print_info_for_predicates "****** Before preprocess:" phis; phis)
  |> (fun phis -> if config.preprocess then Preprocessor.elim_pvars phis else phis)
  |> (fun phis -> print_info_for_predicates "****** After preprocess:" phis; phis)
  |> List.rev_map ~f:(fun phi -> Constraint.Formula phi)
  |> (fun constraints -> print_psat_problem phis constraints; constraints)
  |> synth_predicates
  |> function
    | (Some sol), iteration ->
        let sol = if config.complete_solution then complete_solution phis sol else sol in
        Debug.print "Solution:";
        Debug.print @@ PrinterHum.str_of_candidates sol ^ "\n";
        if config.check_ans then check_ans phis sol else ();
        Status.Sat, iteration
    | None, iteration -> Status.UnSat, iteration
