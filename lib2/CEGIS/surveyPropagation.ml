open Fptprover
open Ast.Proplogic

module Ident = Ast.Ident

type 't signed = Negative of 't | Positive of 't

let unsign = function | Negative t | Positive t -> t

module FactorGraph = struct
	exception Trivial_conflict

	type clause = int
	type variable = string

	type t =
		{
			mutable clause_count : int;
			clauses : (clause, variable signed list) Hashtbl.t;
			variables : (variable, clause signed) Hashtbl.t;
			valuation : (variable, bool) Hashtbl.t
		}

	let make () =
		{
			clause_count = 0;
			clauses = Hashtbl.create 100;
			variables = Hashtbl.create 100;
			valuation = Hashtbl.create 100
		}
	
	let init builder =
		let graph = make () in
			builder graph; graph
	
	let copy graph =
		{graph with
			clauses = Hashtbl.copy graph.clauses;
			variables = Hashtbl.copy graph.variables;
			valuation = Hashtbl.copy graph.valuation}

	let variables_of graph =
		Hashtbl.fold (fun variable _ variables ->
			if List.mem variable variables then
				variables
			else
				variable :: variables) graph.variables []

	let clauses_of graph =
		Hashtbl.fold (fun clause _ clauses ->
			if List.mem clause clauses then
				clauses
			else
				clause :: clauses) graph.clauses []

	let signed_variables_of_clause graph clause =
		Hashtbl.find graph.clauses clause

	let variables_of_clause graph clause =
		Hashtbl.find graph.clauses clause |> List.map unsign

	let signed_clauses_of_variable graph variable =
		Hashtbl.find_all graph.variables variable

	let clauses_of_variable graph variable =
		Hashtbl.find_all graph.variables variable |> List.map unsign

	let iter_clause graph iterate =
		Hashtbl.fold (fun clause _ () ->
			iterate clause) graph.clauses ()

	let valuation_of graph =
		Hashtbl.fold (fun variable boolean valuation ->
			(variable, boolean) :: valuation) graph.valuation []
	
	let rec reduce graph variable sign =
		let (satisfied, unsatisfied) = signed_clauses_of_variable graph variable
			|> List.partition (function | Negative _ -> not sign | Positive _ -> sign)
			|> fun (satisfied, unsatisfied) -> (List.map unsign satisfied, List.map unsign unsatisfied) in

		if Hashtbl.mem graph.valuation variable then
			if Hashtbl.find graph.valuation variable = sign then
				()
			else
				raise Trivial_conflict
		else begin
			Hashtbl.add graph.valuation variable sign;

			while Hashtbl.mem graph.variables variable do
				Hashtbl.remove graph.variables variable
			done;

			List.iter (fun clause ->
				let rec remove stashed variable =
					match Hashtbl.find graph.variables variable with
					| Negative clause' | Positive clause'  when clause = clause' ->
						Hashtbl.remove graph.variables variable;
						List.iter (Hashtbl.add graph.variables variable) stashed
					| signed_clause ->
						Hashtbl.remove graph.variables variable;
						remove (signed_clause :: stashed) variable in

				variables_of_clause graph clause
				|> List.filter ((<>) variable)
				|> List.iter (remove []);

				Hashtbl.remove graph.clauses clause) satisfied;

			let units = List.fold_left (fun units clause ->
				Hashtbl.find graph.clauses clause
				|> List.filter (function | Negative variable' | Positive variable' -> variable <> variable')
				|> function
					| [] -> raise Trivial_conflict
					| [literal] ->
						Hashtbl.replace graph.clauses clause [literal];
						literal :: units
					| literals ->
						Hashtbl.replace graph.clauses clause literals;
						units) [] unsatisfied in

			List.iter (function
				| Negative variable ->
					reduce graph variable false
				| Positive variable ->
					reduce graph variable true) units
		end

	let add graph negatives positives =
		match (negatives, positives) with
		| ([], []) ->
			raise Trivial_conflict
		| ([variable], []) ->
			reduce graph variable false
		| ([], [variable]) ->
			reduce graph variable true
		| _ when List.exists (fun variable -> List.mem variable positives) negatives -> ()
		| _ ->
			let clause = graph.clause_count in
			let negatives' = List.fold_left (fun distinct variable ->
				if List.mem variable distinct then distinct else variable :: distinct) [] negatives
					|> List.map (fun variable -> Negative variable) in
			let positives' = List.fold_left (fun distinct variable ->
				if List.mem variable distinct then distinct else variable :: distinct) [] positives
					|> List.map (fun variable -> Positive variable) in
			let literals = negatives' @ positives' in

			Hashtbl.add graph.clauses clause literals;

			List.iter (fun literal ->
				match literal with
				| Negative variable ->
					Hashtbl.add graph.variables variable (Negative clause)
				| Positive variable ->
					Hashtbl.add graph.variables variable (Positive clause)) literals;

			graph.clause_count <- 1 + clause

	let to_formula graph =
		Formula.and_of (Hashtbl.fold (fun _ clause conjunction ->
			Formula.or_of (List.map (function
				| Negative variable ->
					Formula.mk_neg (Formula.mk_atom variable Dummy) Dummy
				| Positive variable ->
					Formula.mk_atom variable Dummy) clause) Dummy :: conjunction) graph.clauses []) Dummy
end

module SP = struct
	exception Conflict

	type t =
		{
			graph : FactorGraph.t;
			etas : (FactorGraph.clause * FactorGraph.variable, float) Hashtbl.t;
			pis : (FactorGraph.variable * FactorGraph.clause, float) Hashtbl.t
		}


		let make graph =
			let etas = Hashtbl.create 100 in
			let pis = Hashtbl.create 100 in

			FactorGraph.iter_clause graph (fun clause ->
				FactorGraph.variables_of_clause graph clause |> List.iter (fun variable ->
					Hashtbl.replace etas (clause, variable) @@ Random.float 1.;
					Hashtbl.replace pis (variable, clause) @@ Random.float 1.));

			{graph; etas; pis}
	
	let derive sp graph =
		let etas = Hashtbl.create 100 in
		let pis = Hashtbl.create 100 in

		FactorGraph.iter_clause graph (fun clause ->
			FactorGraph.variables_of_clause graph clause |> List.iter (fun variable ->
				Hashtbl.add etas (clause, variable) @@ Hashtbl.find sp.etas (clause, variable);
				Hashtbl.add pis (variable, clause) @@ Hashtbl.find sp.pis (variable, clause)));

		{graph; etas; pis}

	let estimate_eta sp clause variable =
		FactorGraph.variables_of_clause sp.graph clause |> List.filter ((<>) variable)
		|> List.fold_left (fun product variable ->
			product *. Hashtbl.find sp.pis (variable, clause)) 1.

	let estimate_pi sp variable clause =
		let estimate clause' = Hashtbl.find sp.etas (clause', variable) in
		let clauses = FactorGraph.signed_clauses_of_variable sp.graph variable in
		let (evens, odds) =
			List.filter (function | Negative clause' | Positive clause' -> clause <> clause') clauses
			|> begin
				if List.mem (Negative clause) clauses then
					List.partition (function | Negative _ -> true | Positive _ -> false)
				else if List.mem (Positive clause) clauses then
					List.partition (function | Negative _ -> false | Positive _ -> true)
				else
					failwith "given variable not in given clause" end
			|> fun (evens, odds) ->
				(List.map unsign evens, List.map unsign odds) in

		let evens_pi = evens
			|> List.fold_left (fun product clause -> product *. (1. -. estimate clause)) @@
				1. -. List.fold_left (fun product clause -> product *. (1. -. estimate clause)) 1. evens
			|> fun pi -> 1. -. pi in

		let odds_pi = odds
			|> List.fold_left (fun product clause -> product *. (1. -. estimate clause)) @@
				1. -. List.fold_left (fun product clause -> product *. (1. -. estimate clause)) 1. odds
			|> fun pi -> 1. -. pi in


		odds_pi *. (1. -. evens_pi) /. (1. -. evens_pi *. odds_pi)
	
	let update sp =
		let delta = ref 0. in

		FactorGraph.iter_clause sp.graph (fun clause ->
			FactorGraph.variables_of_clause sp.graph clause |> List.iter (fun variable ->
				let eta = Hashtbl.find sp.etas (clause, variable) in
				let pi = Hashtbl.find sp.pis (variable, clause) in
				let eta' = estimate_eta sp clause variable in
				let pi' = estimate_pi sp variable clause in

				delta := max !delta @@ abs_float (eta -. eta');
				delta := max !delta @@ abs_float (pi -. pi');

				Hashtbl.replace sp.etas (clause, variable) eta';
				Hashtbl.replace sp.pis (variable, clause) pi'));

		!delta

	let update_to_converge sp =
		let rec loop n =
			if n = 100 then
				false
			else if update sp > 0.01 then
				loop (n + 1)
			else
				(Debug.print @@ "converged in " ^ string_of_int n ^ " iterations"; true) in

		loop 0

	let marginalize' sp variable =
		let estimate clause = Hashtbl.find sp.etas (clause, variable) in
		let clauses = FactorGraph.signed_clauses_of_variable sp.graph variable in
		let (positives, negatives) = List.partition (function | Negative _ -> false | Positive _ -> true) clauses
			|> fun (positives, negatives) -> (List.map unsign positives, List.map unsign negatives) in

		let positive_pi = positives
			|> List.fold_left (fun product clause -> product *. (1. -. estimate clause)) @@
				1. -. List.fold_left (fun product clause -> product *. (1. -. estimate clause)) 1. positives
			|> fun pi -> 1. -. pi in

		let negative_pi = negatives
			|> List.fold_left (fun product clause -> product *. (1. -. estimate clause)) @@
				1. -. List.fold_left (fun product clause -> product *. (1. -. estimate clause)) 1. negatives
			|> fun pi -> 1. -. pi in

		(positive_pi *. (1. -. negative_pi) /. (1. -. positive_pi *. negative_pi),
		 negative_pi *. (1. -. positive_pi) /. (1. -. positive_pi *. negative_pi))

	let complexity sp =
		let first = FactorGraph.variables_of sp.graph
			|> List.fold_left (fun sum variable ->
				let (weight_positive, weight_negative) = marginalize' sp variable in
					sum +. log (1. -. weight_positive *. weight_negative)) 0. in

		let second = FactorGraph.clauses_of sp.graph
			|> List.fold_left (fun sum clause ->
				let n = List.length @@ FactorGraph.variables_of_clause sp.graph clause in
				let product = FactorGraph.variables_of_clause sp.graph clause
					|> List.fold_left (fun product variable ->
						product *. Hashtbl.find sp.pis (variable, clause)) 1. in

				sum +. (1. -. float_of_int n) *. log (1. -. product)) 0. in

		first +. second

	let marginalize sp variable =
		let (weight_positive, weight_negative) = marginalize' sp variable in
			(1. -. min weight_positive weight_negative, weight_positive, weight_negative)
	
	let aggregate sp =
		FactorGraph.variables_of sp.graph
		|> List.map (fun variable ->
			let (bias, weight_positive, weight_negative) = marginalize sp variable in
				(variable, bias, weight_positive, weight_negative))
		|> List.sort (fun (_, bias, _, _) (_, bias', _, _) -> -compare bias bias')
end

module Solver = struct
	let rec decimate sp graph =
		let valuation = FactorGraph.valuation_of graph in

		if FactorGraph.variables_of graph = [] then
			let _ = Debug.print @@ "totally solved: " ^ string_of_int (List.length valuation) ^ " decided\n" in
				valuation
		else if SP.update_to_converge sp then
			let _ = Debug.print @@ "complexity: " ^ string_of_float (SP.complexity sp) ^ "\n" in
			let marginals = SP.aggregate sp |> List.filter (fun (_, bias, _, _) -> bias > 0.9) in

			let rec decimate' n = function
				| [] ->
					Debug.print @@ "reached trivial cover: " ^
						string_of_int (List.length valuation) ^ " decided of " ^
						string_of_int (List.length valuation + List.length (FactorGraph.variables_of graph)) ^ " \n";

					begin match Smt.Z3interface.SAT.check_sat (FactorGraph.to_formula graph) with
					| None -> Debug.print "unsatisfiabiable solution\n"; []
					| Some _ -> Debug.print "satisfiable solution\n"; valuation end
				| (variable, bias, weight_positive, weight_negative) :: marginals ->
					let boolean = weight_positive > weight_negative in

					Debug.print @@ "decide [" ^ variable ^ "] = " ^ string_of_bool boolean ^ " with bias = " ^ string_of_float bias ^ "\n";

					match FactorGraph.reduce graph variable boolean with
					| exception FactorGraph.Trivial_conflict ->
						Debug.print "decimation failed\n"; []
					| () ->
						if n = 0 then
							decimate (SP.derive sp graph) graph
						else
							decimate' (n - 1) marginals in

			let n = int_of_float @@ max 1. (log (float_of_int (List.length (FactorGraph.variables_of graph)))) in
				decimate' n marginals
		else
			begin
				Debug.print "unconverged\n";
				[]
			end

	let solve clauses =
		let graph = FactorGraph.init (fun graph ->
			List.iter (fun (negatives, positives) -> FactorGraph.add graph negatives positives) clauses) in

		decimate (SP.make graph) graph
end

module SAT = struct
	let check_sat formula =
		Solver.solve (Logicutil.tseitinize formula) |> fun some -> Some some
end
