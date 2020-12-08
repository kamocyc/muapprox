open Ast
open Ast.Logic
open Core open Core.Poly

module Debug = Fptprover.Debug

type info_preds = (Ident.pvar * Sort.t list * bool) list
type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS

let ty_ex_info = TyEXPICS

let label_of (Ident.Pvar name) disjunct_index qualifier_index =
  String.concat ~sep:"-" [name; string_of_int disjunct_index; string_of_int qualifier_index]

let evaluate halfspace params arguments =
  let parameters = List.map ~f:fst params in
  let valuation = List.zip_exn parameters arguments |> Core.Map.Poly.of_alist_exn in
  let formula' = Formula.subst valuation halfspace in

  Logicutil.eval_formula formula'

let abstract_application pvar disjunction qualifier_indices =
  let app_var = match Ident.mk_fresh_pvar () with | Ident.Pvar name -> name in
  let tseitin_of disjunct_index = app_var ^ "-" ^ string_of_int disjunct_index in

  if List.length disjunction = 1 then
    (app_var,
     ([], app_var :: List.map ~f:(label_of pvar 0) qualifier_indices) ::
     List.map ~f:(fun qualifier_index ->
         ([app_var; label_of pvar 0 qualifier_index], [])) qualifier_indices)
  else
    (app_var,
     ([app_var],
      List.mapi ~f:(fun disjunct_index _ -> tseitin_of disjunct_index) disjunction) ::
     List.mapi ~f:(fun disjunct_index _ ->
         ([], app_var ::
              List.map ~f:(label_of pvar disjunct_index) qualifier_indices)) disjunction @
     List.mapi ~f:(fun disjunct_index _ ->
         ([], tseitin_of disjunct_index ::
              List.map ~f:(label_of pvar disjunct_index) qualifier_indices)) disjunction @
     List.fold_left qualifier_indices ~init:[] ~f:(fun clauses qualifier_index ->
         List.rev_append clauses @@
         List.mapi ~f:(fun disjunct_index  _ ->
             ([tseitin_of disjunct_index; label_of pvar disjunct_index qualifier_index], [])) disjunction))

let rec mk_candidates default_quals_map signature sample disjunction =
  let config = !Fptprover.Global.config in
  let disjunction_of_pred _pvar = Array.init disjunction ~f:(fun i -> i) |> Array.to_list in

  let qualifiers =
    List.map ~f:(fun (pvar, sorts, _wf) ->
        Set.Poly.iter sample ~f:(fun clause ->
            let pos =
              clause.ExampleInstance.positive
              |> Set.Poly.map ~f:ExampleInstance.str_of_example
              |> Set.Poly.to_list
              |> String.concat ~sep:","
            in
            let neg =
              clause.ExampleInstance.negative
              |> Set.Poly.map ~f:ExampleInstance.str_of_example
              |> Set.Poly.to_list
              |> String.concat ~sep:","
            in
            Debug.print @@ "* " ^ pos ^ " <= " ^ neg  ^ "\n");

        let examples =
          sample
          |> Set.Poly.to_list
          |> List.map ~f:(fun clause ->
              Set.Poly.union
                clause.ExampleInstance.positive
                clause.ExampleInstance.negative
              |> Set.Poly.filter_map ~f:(function
                  | ExampleInstance.PApp ((pvar', sorts'), arguments) ->
                    if pvar = pvar' then Some((pvar', sorts'), arguments) else None
                  | _ -> None))
          |> Set.Poly.union_list
        in

        let (params, qualifiers) = Template.gen_half_spaces sorts examples in
        let qualifiers = Set.Poly.add qualifiers (Formula.or_of [] Dummy) in

        let default_quals =
          match List.Assoc.find default_quals_map ~equal:(=) pvar with
          | None -> Set.Poly.empty
          | Some q -> q
        in
        let qualifiers = Set.Poly.to_list @@ Set.Poly.union default_quals qualifiers in
        Debug.print "QUALIFIERS: ";
        Debug.print @@ Template.str_of_qualifiers qualifiers ^ "\n";

        (pvar, (params, qualifiers))) signature in

  let application_to_variable = Hashtbl.Poly.create ~size:100 () in

  let abstract_application' sign opt member =
    match opt with
    | None -> None
    | Some (variables, subconstraints) ->
      begin match (sign, member) with
        | (false, ExampleInstance.False) -> None
        | (false, ExampleInstance.True) -> Some (variables, subconstraints)
        | (true, ExampleInstance.False) -> Some (variables, subconstraints)
        | (true, ExampleInstance.True) -> None
        | (_, ExampleInstance.PApp ((pvar, _sorts), arguments)) ->
          if Hashtbl.Poly.mem application_to_variable (pvar, arguments) then
            let variable = Hashtbl.Poly.find_exn application_to_variable (pvar, arguments) in
            Some (variable :: variables, subconstraints)
          else
            begin
              let (params, qualifiers') = List.Assoc.find_exn ~equal:(=) qualifiers pvar in
              let qualifier_indices =
                List.mapi ~f:(fun index qualifier -> (index, qualifier)) qualifiers'
                |> List.filter ~f:(fun (_, qualifier) -> not (evaluate qualifier params arguments))
                |> List.map ~f:fst
              in

              let (variable, subconstraints') =
                abstract_application pvar (disjunction_of_pred pvar) qualifier_indices
              in

              Hashtbl.Poly.add_exn application_to_variable ~key:(pvar, arguments) ~data:variable;
              Some (variable :: variables, List.rev_append subconstraints' subconstraints)
            end
      end in

  let abstraction =
    sample
    |> Set.Poly.to_list
    |> List.fold_left ~init:[] ~f:(fun cnf clause ->
        clause.ExampleInstance.negative
        |> Set.Poly.to_list
        |> List.fold_left ~init:(Some ([], [])) ~f:(abstract_application' false)
        |> function
        | None -> cnf
        | Some (negatives, subconstraints) ->
          clause.ExampleInstance.positive
          |> Set.Poly.to_list
          |> List.fold_left ~init:(Some ([], subconstraints)) ~f:(abstract_application' true)
          |> (function
              | None -> cnf
              | Some (positives, subconstraints) ->
                (negatives, positives) :: List.rev_append subconstraints cnf))
  in

  Debug.print "ABSTRACTED: ";

  List.iter ~f:(fun (negatives, positives) ->
      Debug.print @@ "* " ^ String.concat ~sep:" " negatives;
      Debug.print @@ "  => " ^ String.concat ~sep:" " positives) abstraction;

  let capital_solution = Zecchina.SAT.solve_partially abstraction in
  let residual_solutions = Zecchina.SAT.solve_and_seek config.multisol @@
    Zecchina.SAT.reduce_cnf capital_solution abstraction in
  let residual_solutions =
    if config.dim_reduction then
      (* Dimensionality Reduction on bPCSs *)
      ExampleInstance.minimize_core_for_bSPC abstraction residual_solutions
    else residual_solutions in

  if residual_solutions = [] then
    begin
      Debug.print "UNSAT\n";
      mk_candidates default_quals_map signature sample (disjunction + 1)
    end
  else
    begin
      Debug.print "SAT\n";
      residual_solutions
      |> List.sort ~compare:(fun a b -> Zecchina.SAT.count_false b - Zecchina.SAT.count_false a)
      |> List.map ~f:(fun residual_solution ->
          let solution = capital_solution @ residual_solution in
          List.map ~f:(fun (pvar, _sorts, _wf) ->
              let (params, qualifiers') = List.Assoc.find_exn ~equal:(=) qualifiers pvar in
              let formula =
                disjunction_of_pred pvar
                |> List.mapi ~f:(fun disjunct_index _ ->
                    snd @@ List.fold_left qualifiers' ~init:(0, [])
                      ~f:(fun (qualifier_index, clause) qualifier ->
                          let label = label_of pvar disjunct_index qualifier_index in
                          if List.Assoc.mem ~equal:(=) solution label && List.Assoc.find_exn ~equal:(=) solution label then
                            (qualifier_index + 1, qualifier :: clause)
                          else
                            (qualifier_index + 1, clause))
                    |> fun literals -> Formula.and_of literals Dummy)
                |> fun clauses -> Formula.or_of clauses Dummy in

              Debug.print @@ (match pvar with Ident.Pvar name -> name) ^ " is ... ";
              Debug.print @@ Convert.PrinterHum.str_of_formula formula ^ "\n";
              ((pvar, params), formula)) signature)
    end

let mk_candidates ex_info (sample : ExampleInstance.t) =
  let config = !Fptprover.Global.config in

  match ex_info with
  | EXPICS (signature, cs) ->
    let default_qualifier = if config.default_qualifier then Template.get_default_qualifiers cs else [] in
    mk_candidates default_qualifier signature sample config.number_of_disj
