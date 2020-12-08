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
     String.concat "-" [name; string_of_int disjunct_index; string_of_int qualifier_index]

let evaluate halfspace params arguments =
  let parameters = List.map fst params in
  let valuation = List.combine parameters arguments in
  let formula' = Formula.subst valuation halfspace in
  
  Logicutil.eval_formula formula'

let abstract_literal disjunction_of_pred qualifiers literal =
	match literal with
	| ExampleConstraint.True -> Proplogic.Formula.True Proplogic.Dummy
	| ExampleConstraint.False -> Proplogic.Formula.False Proplogic.Dummy
	| ExampleConstraint.PApp ((pvar, _sorts), arguments) ->
		disjunction_of_pred pvar |> List.mapi (fun disjunct_index _ ->
			let (params, qualifiers') = List.assoc pvar qualifiers in

			fst @@ List.fold_left (fun (literals, qualifier_index) qualifier ->
				let label = label_of pvar disjunct_index qualifier_index in

				if evaluate qualifier params arguments then
					(literals, qualifier_index + 1)
				else
					let literal = Proplogic.Formula.mk_neg (Proplogic.Formula.Atom (label, Proplogic.Dummy)) Proplogic.Dummy in
						(literal :: literals, qualifier_index + 1)) ([], 0) qualifiers'
			|> fun literals -> Proplogic.Formula.and_of literals Proplogic.Dummy)
		|> fun clauses -> Proplogic.Formula.or_of clauses Proplogic.Dummy

let rec mk_candidates signature sample disjunction =
  let config = !Fptprover.Global.config in
	let disjunction_of_pred _pvar = Array.init disjunction (fun i -> i) |> Array.to_list in

	let qualifiers = List.map (fun (pvar, sorts, _wf) ->
		List.iter (fun clause ->
			Debug.print "* "; Debug.print @@ ExampleConstraint.str_of_examples "," clause.ExampleConstraint.positive;
			Debug.print " <= "; Debug.print @@ ExampleConstraint.str_of_examples "," clause.ExampleConstraint.negative ^ "\n") sample;

		let examples = List.fold_left (fun examples clause ->
			clause.ExampleConstraint.positive @ clause.ExampleConstraint.negative
				|> List.fold_left (fun examples example ->
					match example with
						| ExampleConstraint.PApp ((pvar', sorts'), arguments) ->
							if pvar = pvar' then  ((pvar', sorts'), arguments) :: examples else examples
						| _ -> examples) examples) [] sample in

		let (params, qualifiers) = Template.gen_half_spaces sorts examples
		let qualifiers = Formula.or_of [] Dummy :: qualifiers
			@ List.map (fun qualifier -> Formula.mk_neg qualifier Dummy) qualifiers in

		Debug.print "QUALIFIERS: ";
		Debug.print @@ Template.str_of_qualifiers qualifiers ^ "\n";

		(pvar, (params, qualifiers))) signature in
	let abstract_literal' = abstract_literal disjunction_of_pred qualifiers in
	let abstraction =
		List.map (fun clause ->
			let positives' = clause.ExampleConstraint.positive |> List.map abstract_literal' in
			let negatives' = clause.ExampleConstraint.negative |> List.map (fun literal ->
				Proplogic.Formula.mk_neg (abstract_literal' literal) Proplogic.Dummy) in

			Proplogic.Formula.or_of (positives' @ negatives') Proplogic.Dummy) sample
		|> fun clauses -> Proplogic.Formula.and_of clauses Dummy in

	Debug.print "ABSTRACTED: ";
	Debug.print @@ Proplogic.Formula.str_of abstraction ^ "\n";

	let abstraction = Logicutil.tseitinize abstraction in
	let capital_solution = Zecchina.SAT.solve_partially abstraction in
	let residual_solutions = Zecchina.SAT.solve_and_seek config.multisol @@
		Zecchina.SAT.reduce_cnf capital_solution abstraction in

	if residual_solutions = [] then
		begin
			Debug.print "UNSAT\n";
			mk_candidates signature sample (disjunction + 1)
		end
	else
		begin
			Debug.print "SAT\n";
			List.sort (fun a b -> Zecchina.SAT.count_false b - Zecchina.SAT.count_false a) residual_solutions
			|> List.map (fun residual_solution ->
				let solution = capital_solution @ residual_solution in

				List.map (fun (pvar, _sorts, _wf) ->
					let (params, qualifiers') = List.assoc pvar qualifiers in
					let formula = disjunction_of_pred pvar
						|> List.mapi (fun disjunct_index _ ->
							snd @@ List.fold_left (fun (qualifier_index, clause) qualifier ->
								let label = label_of pvar disjunct_index qualifier_index in

								if List.mem_assoc label solution && List.assoc label solution then
									(qualifier_index + 1, qualifier :: clause)
								else
									(qualifier_index + 1, clause)) (0, []) qualifiers'
							|> fun literals -> Formula.and_of literals Dummy)
						|> fun clauses -> Formula.or_of clauses Dummy in

					Debug.print @@ (match pvar with Ident.Pvar name -> name) ^ " is ... ";
					Debug.print @@ Convert.PrinterHum.str_of_formula formula ^ "\n";
					((pvar, params), formula)) signature)
		end

let mk_candidates ex_info (sample : ExampleConstraint.t) =
	let config = !Fptprover.Global.config in

	match ex_info with
	| EXPICS (signature, _) ->
		mk_candidates signature sample config.number_of_disj
