open Core open Core.Poly
open Ast
open Ast.Logic

module Debug = Fptprover.Debug

type info_preds = (Ident.pvar * Sort.t list * bool) list
type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                         * Constraint.t list
type ty_ex_info = TyEXPICS

let ty_ex_info = TyEXPICS

let label_of pvar disjunct_index qualifier_index =
  match pvar with
  | Ident.Pvar name ->
    String.concat ~sep:"-" [name; string_of_int disjunct_index; string_of_int qualifier_index]

let evaluate halfspace params arguments =
  let parameters = List.map ~f:fst params in
  let valuation = List.zip_exn parameters arguments |> Map.Poly.of_alist_exn in
  let formula' = Formula.subst valuation halfspace in

  Logicutil.eval_formula formula'

let abstract_literal disjunction_of_pred qualifiers literal =
  match literal with
  | ExampleInstance.True -> Proplogic.Formula.True Proplogic.Dummy
  | ExampleInstance.False -> Proplogic.Formula.False Proplogic.Dummy
  | ExampleInstance.PApp ((pvar, _sorts), arguments) ->
    disjunction_of_pred pvar
    |> List.mapi ~f:(fun disjunct_index _ ->
        let (params, qualifiers') = List.Assoc.find_exn ~equal:(=) qualifiers pvar in

        fst @@ List.fold_left qualifiers' ~init:([], 0)
          ~f:(fun (literals, qualifier_index) qualifier ->
              let label = label_of pvar disjunct_index qualifier_index in

              if evaluate qualifier params arguments then
                (literals, qualifier_index + 1)
              else
                let literal = Proplogic.Formula.mk_neg
                    (Proplogic.Formula.Atom (label, Proplogic.Dummy))
                    Proplogic.Dummy
                in
                (literal :: literals, qualifier_index + 1))
        |> fun literals -> Proplogic.Formula.and_of literals Proplogic.Dummy)
    |> fun clauses -> Proplogic.Formula.or_of clauses Proplogic.Dummy

let rec mk_candidates default_quals_map signature sample disjunction =
  let config = !Fptprover.Global.config in
  let disjunction_of_pred _pvar = Array.init disjunction ~f:(fun i -> i) |> Array.to_list in

  let qualifiers =
    List.map ~f:(fun (pvar, sorts, _wf) ->
        Set.Poly.iter ~f:(fun clause ->
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
            Debug.print @@ "* " ^ pos ^ " <= " ^ neg  ^ "\n") sample;

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
  let abstract_literal' = abstract_literal disjunction_of_pred qualifiers in
  let abstraction =
    sample
    |> Set.Poly.to_list
    |> List.map ~f:(fun clause ->
        let positives' =
          clause.ExampleInstance.positive
          |> Set.Poly.map ~f:abstract_literal'
          |> Set.Poly.to_list
        in
        let negatives' =
          clause.ExampleInstance.negative
          |> Set.Poly.map ~f:(fun lit -> Proplogic.Formula.mk_neg (abstract_literal' lit)
                                 Proplogic.Dummy)
          |> Set.Poly.to_list
        in

        Proplogic.Formula.or_of (positives' @ negatives') Proplogic.Dummy)
    |> fun clauses -> Proplogic.Formula.and_of clauses Dummy in

  Debug.print "ABSTRACTED: ";
  Debug.print @@ Proplogic.Formula.str_of abstraction ^ "\n";

  match Smt.Z3interface.SAT.solve_and_seek config.multisol abstraction with
  | [] ->
    mk_candidates default_quals_map signature sample (disjunction + 1)
  | solutions ->
    begin
      Debug.print @@ "abstraction: " ^ (Proplogic.Formula.str_of abstraction);
      let solutions = if config.dim_reduction
        then
          let abstraction = Proplogic.Formula.(cnf_of @@ nnf_of abstraction) in
          ExampleInstance.minimize_core_for_bSPC abstraction solutions
        else solutions in
      Debug.print "SAT\n";

      List.sort ~compare:(fun a b ->
          Zecchina.SAT.count_false b - Zecchina.SAT.count_false a) solutions
      |> List.map ~f:(fun solution ->
          List.map ~f:(fun (pvar, _sorts, _) ->
              let (params, qualifiers') =
                List.Assoc.find_exn ~equal:(=) qualifiers pvar
              in
              let formula =
                disjunction_of_pred pvar
                |> List.mapi ~f:(fun disjunct_index _ ->
                    List.mapi ~f:(fun qualifier_index qualifier ->
                        let label = label_of pvar disjunct_index qualifier_index in

                        if List.Assoc.mem ~equal:(=) solution label && List.Assoc.find_exn ~equal:(=) solution label then
                          qualifier
                        else
                          Formula.Atom (Atom.True Dummy, Dummy)) qualifiers'
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
