open Synthesizer
open Core
open Ast.Logic
open Fptprover
open Convert
   
module Make (Synthesizer: SynthesizerType) = struct

  let print_hr ()=
    Debug.print "==========================================================="
    
  let print_problem phi (desugared: Formula.t option) cs =
    Debug.print @@ "parsed : " ^ (PrinterHum.str_of_formula phi);
    let () = match desugared with
      | Some (desugared) ->
         Debug.print @@ "desugared : " ^ (PrinterHum.str_of_formula desugared)
    | None -> () in
    Debug.print @@
      "extracted constraints : " ^ (Constraint.string_of_constraints cs)
    
  let print_iteration ct =
    Debug.print "-----------------------------------------";
    Debug.print @@ "iteration : " ^ (string_of_int ct)
    
  let print_candidate cand =
    Debug.print @@ "predicate assignment candidate : " ^ (PrinterHum.str_of_candidates cand)

  let print_candidates cands =
    Debug.print "************* Predicate Assignment Candidates ************";
    let rec inner counter = function
      | [] -> Debug.print "\n"
      | h::tl -> 
         Debug.print (Printf.sprintf "The %dth candidate:" counter);
         print_candidate h;
         inner (counter + 1) tl
    in inner 0 cands

  let print_new_examples ex =
    Debug.print @@
      "new example constraints:[\n"
      ^ (ExampleInstance.str_of ex) ^ "\n]\n"

  let print_sample sample =
    Debug.print @@
      "all sample:[\n"
      ^ (ExampleInstance.str_of sample) ^ "\n]\n"

  let ex_range = [1; 2; 4; 8; 16]

  let mk_range_constraint phi range =
    let open Ast.Gather in
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
               
  let make_example_with_exr cand formula =
    let rec refine default level =
      match List.nth ex_range level with
      | None -> default
      | Some range ->
         let phi = Formula.subst_preds cand formula in
         let range = mk_range_constraint phi range in
         match Smt.Z3interface.check_validity_with_range range phi with
         | None -> refine default (level+1)
         | Some(model) ->
            Fptprover.Debug.print
            @@ "range:" ^
                 (Convert.PrinterHum.str_of_formula range);
            ExampleInstance.of_model formula model
    in
    let phi = Formula.subst_preds cand formula in
    match Smt.Z3interface.check_validity phi with
    | None -> Set.Poly.empty
    | Some model ->
       let default = (ExampleInstance.of_model formula model) in
       if ExampleInstance.is_in_range 1 default then default
       else refine default 0

  let make_example cand formula =
(*    print_endline @@ "formula@make_example: " ^ (Convert.PrinterHum.str_of_formula formula); *)
    let phi = Formula.subst_preds cand formula in
    match Smt.Z3interface.check_validity phi with
    | None -> Set.Poly.empty
    | Some model -> ExampleInstance.of_model formula model

  let mk_ex_info pinfo cs = (* TODO : option in config *)
    match Synthesizer.ty_ex_info with
    | Synthesizer.TyEXPICS -> Synthesizer.EXPICS(pinfo, cs)

  let solve cs =
    Fptprover.Debug.print "call synth_predicate";
    let config = !Fptprover.Global.config in
    let make_example = if config.example_restriction
                       then make_example_with_exr else make_example in
    let max_iteration = 100 in (* TODO: move this into config.ml *)
    let pinfo, formulas = Constraint.pinfo_and_formula cs in
    let rec validate sample = function
      | [] -> None, sample
      | c::cs ->
         let cand_map = c
             |> List.map ~f:(fun ((pvar, params), formula) -> pvar, (params, formula))
             |> Map.Poly.of_alist_exn
         in
         let new_eg =
           List.map formulas ~f:(make_example cand_map) |> Set.Poly.union_list
         in
         print_new_examples new_eg;
         if Set.Poly.is_empty new_eg then (Some(c), Set.Poly.empty)
         else validate (Set.Poly.union new_eg sample) cs
    in
    let f = Synthesizer.mk_candidates (mk_ex_info pinfo cs) in
    let rec inner counter (sample:ExampleInstance.t) =
      print_iteration counter; ignore(max_iteration);
      if ExampleInstance.contradict sample then None, counter
      else
        begin
          f sample
          |> List.map ~f:(List.map ~f:(fun (target, phi) -> target, Logicutil.normalize_formula phi))
          |> function
            | [] -> failwith "Every synthesizer must generate at least 1 predicate candidates for any inputs."
            | candidates ->
               begin
                 print_candidates candidates;
                 match validate sample candidates with
                 | Some sol , _ -> 
                    Fptprover.Debug.print "synth_predicate : DONE!\n";
                    Some sol, counter
                 | None, sample -> inner (counter+1) sample
               end
        end
    in inner 0 Set.Poly.empty
end
