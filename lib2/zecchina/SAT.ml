external solve : (int list * int list) list -> int array -> unit = "solve"

open Ast.Proplogic

let number_cnf cnf =
	let table = Hashtbl.create 100 in
	let number variable =
		if Hashtbl.mem table variable then
			Hashtbl.find table variable
		else
			let index = Hashtbl.length table in
				Hashtbl.add table variable index; index in

	let cnf' = List.map (fun (negatives, positives) ->
		(List.map number negatives, List.map number positives)) cnf in
	
	(cnf', table)

let rec reduce_cnf assignment cnf =
	match assignment with
	| [] -> cnf
	| (variable, false) :: assignment' ->
		reduce_cnf assignment' @@ List.fold_left (fun clauses (negatives, positives) ->
			if List.exists ((=) variable) negatives then
				clauses
			else
				let positives' = List.filter ((<>) variable) positives in
					(negatives, positives') :: clauses) [] cnf
	| (variable, true) :: assignment' ->
		reduce_cnf assignment' @@ List.fold_left (fun clauses (negatives, positives) ->
			if List.exists ((=) variable) positives then
				clauses
			else
				let negatives' = List.filter ((<>) variable) negatives in
					(negatives', positives) :: clauses) [] cnf

let formula_of_cnf cnf =
	List.map (fun (negatives, positives) ->
		Formula.or_of
			(List.map (fun variable -> Formula.mk_neg (Formula.mk_atom variable Dummy) Dummy) negatives @
			 List.map (fun variable -> Formula.mk_atom variable Dummy) positives) Dummy) cnf
	|> fun clauses -> Formula.and_of clauses Dummy

let z3_check_cnf cnf =
	match Smt.Z3interface.SAT.check_sat @@ formula_of_cnf cnf with
	| None -> None
	| Some model ->
		List.map (function
			| (Formula.Atom (variable, _), Some (Formula.False Dummy)) ->
				(variable, false)
			| (Formula.Atom (variable, _), Some (Formula.True Dummy)) ->
				(variable, true)
			| _ -> failwith "invalid model") model
		|> fun some -> Some some

let has_prefix string char =
	try String.get string 0 = char with Invalid_argument _ -> false

let count_false assignment =
	List.fold_left (fun falses (variable, boolean) ->
		if boolean || has_prefix variable '#' then falses else 1 + falses) 0 assignment

let solve_partially cnf =
	let (ncnf, table) = number_cnf @@ cnf in
	let buffer = Array.make (Hashtbl.length table) 0 in
	let _ = solve ncnf buffer in

	Hashtbl.fold (fun variable index solution ->
		if buffer.(index) = 0 then
			solution
		else if buffer.(index) > 0 then
			(variable, true) :: solution
		else
			(variable, false) :: solution) table []

let rec solve_and_seek maximum cnf =
	if maximum < 0 then
		failwith "maximum cannot be negative"
	else if maximum = 0 then
		[]
	else
		match z3_check_cnf cnf with
		| None -> []
		| Some solution ->
			let negation = List.fold_left (fun (negatives, positives) (variable, boolean) ->
				if boolean then
					(variable :: negatives, positives)
				else
					(negatives, variable :: positives)) ([], []) solution in

			solution :: solve_and_seek (maximum - 1) (negation :: cnf)

let solve cnf =
	let capital_solution = solve_partially cnf in

	match z3_check_cnf (reduce_cnf capital_solution cnf) with
	| None -> None
	| Some residual_solution ->
		Some (capital_solution @ residual_solution)


let solution_to_model =
  List.map (fun (variable, boolean) -> Formula.mk_atom variable Dummy,
                                       Some (if boolean then Formula.mk_true Dummy
                                             else Formula.mk_false Dummy))

let name_of_prop = function
  | Formula.Atom (name, Dummy) -> name
  | _ -> assert false

let prop_of_name name = Formula.mk_atom name Dummy
let bool_of_prop = function
  | Formula.True Dummy -> true | Formula.False Dummy -> false
  | _ -> assert false
