open Ast
open Ast.Logic
open Core open Core.Poly

(* CNF *)
type t = clause Set.Poly.t
and clause = {positive: example Set.Poly.t ; negative: example Set.Poly.t }
and example = PApp of ((Ident.pvar * Sort.t list) * Term.t list) | True | False

let formula_of_example = function
  | PApp ((pvar, sorts), terms) ->
    Formula.mk_atom
      (Atom.mk_app (Predicate.mk_var pvar sorts) terms Dummy) Dummy
  | True -> Formula.mk_atom (Atom.mk_true Dummy) Dummy
  | False -> Formula.mk_atom (Atom.mk_false Dummy) Dummy
let formula_of_clause clause =
  let neg_formula_of_ex ex = Formula.mk_neg (formula_of_example ex) Dummy in
  let positives =
    clause.positive
    |> Set.Poly.to_list
    |> List.map ~f:formula_of_example
  in
  let negatives =
    clause.negative
    |> Set.Poly.to_list
    |> List.map ~f:neg_formula_of_ex
  in
  Formula.or_of (positives @ negatives) Dummy
let formula_of t = Formula.and_of (t |> Set.Poly.to_list |> List.map ~f:formula_of_clause) Dummy

let str_of_example = function
  | True -> "true" | False -> "false"
  | PApp ((Ident.Pvar ident, _), terms) ->
    let rec str_of_terms = function
      | [] -> ""
      | t::[] -> Convert.PrinterHum.str_of_term t
      | t::ts -> Convert.PrinterHum.str_of_term t ^ "," ^ (str_of_terms ts)
    in
    Printf.sprintf "%s(%s)" ident (str_of_terms terms)
let str_of_clause cl =
  let pos =
    cl.positive
    |> Set.Poly.map ~f:str_of_example
    |> Set.Poly.to_list
    |> String.concat ~sep:"\\/"
  in
  let neg =
    cl.negative
    |> Set.Poly.map ~f:str_of_example
    |> Set.Poly.to_list
    |> String.concat ~sep:"/\\"
  in
  Printf.sprintf "(%s => %s)" neg pos
let str_of ex =
  ex
  |> Set.Poly.map ~f:str_of_clause
  |> Set.Poly.to_list
  |> String.concat ~sep:";\n"
let str_of_maps maps =
  let open Ast in
  maps
  |> List.map ~f:(function
      | (Ident.Tvar tvar, None) ->
        (Printf.sprintf "(%s -> *)" tvar)
      | (Ident.Tvar tvar, Some term) ->
        (Printf.sprintf "(%s -> %s)" tvar
           (Convert.PrinterHum.str_of_term term)))
  |> String.concat

let prop_count = ref 0

let gen_fresh_prop () =
  let open Proplogic in
  prop_count := !prop_count + 1;
  Formula.mk_atom ("A" ^ string_of_int !prop_count) Dummy

let subst_example map =
  let open Proplogic in
  function
  | True -> Formula.mk_true Dummy | False -> Formula.mk_false Dummy
  | PApp ex ->
    match Set.Poly.find_map map ~f:(fun (ex', prop) -> if ex = ex' then Some prop else None) with
    | Some p -> p | None -> assert false

let all_apps_of s =
  s
  |> Set.Poly.map ~f:(fun cl -> Set.Poly.union cl.positive cl.negative)
  |> Set.Poly.to_list
  |> Set.Poly.union_list
  |> Set.Poly.filter_map ~f:(function PApp app -> Some app | _ -> None)

let pred_to_prop (sample:t) =
  sample
  |> all_apps_of
  |> Set.Poly.map ~f:(fun m -> (m, gen_fresh_prop()))

let sat_test () =
  let open Proplogic in
  let open Util in
  let f = Formula.mk_false Dummy in
  let negp = Formula.mk_neg (Formula.mk_atom "P" Dummy) Dummy in
  let phi = Formula.mk_or negp f Dummy in
  Fptprover.Debug.print @@ "test phi:" ^ (Formula.str_of phi);
  Smt.Z3interface.SAT.check_sat phi >>= fun model ->
  Fptprover.Debug.print @@ "test model:" ^ (Convert.PrinterHum.str_of_proplogic_model model);
  Some(true)


let sample_wrt_pred sample pred =
  Set.Poly.filter sample ~f:(fun ((pvar, _), _) -> pvar = pred)

let normalize_example ex =
  match ex with
  | True | False -> ex
  | PApp (target, terms) ->
    PApp(target,
         List.map ~f:(fun term ->
             Logicutil.(eval_term term |> term_of_termlit)) terms)

let normalize_clause cl =
  let pos = Set.Poly.map ~f:normalize_example cl.positive in
  let neg = Set.Poly.map ~f:normalize_example cl.negative in
  {positive=pos; negative=neg}

let normalize = Set.Poly.map ~f:normalize_clause

let simplify_logically =
  Set.Poly.map ~f:(fun cl ->
      if Set.Poly.exists ~f:(function | True -> true | _ -> false) cl.positive
      || Set.Poly.exists ~f:(function | False -> true | _ -> false) cl.negative
      then {positive = Set.Poly.singleton True; negative = Set.Poly.empty}
      else
        { positive = Set.Poly.filter ~f:(function False -> false | _ -> true) cl.positive;
          negative = Set.Poly.filter ~f:(function True -> false | _ -> true) cl.negative })

let rm_obvious_examples =
  let conclude_true  e = Set.Poly.mem e.positive True in
  let false_conclude e = Set.Poly.mem e.negative False in
  Set.Poly.filter ~f:(fun e -> not (conclude_true e) && not (false_conclude e) )

let example_of_atom = function
  | Atom.True _ -> True | Atom.False _ -> False
  | Atom.App (Var(pvar, sorts), terms, _) -> PApp ((pvar, sorts), terms)
  | (Atom.App (Psym _, _, _)) as atom ->
    if Logicutil.eval_formula (Formula.Atom (atom, Dummy)) then True else False
  | _ -> failwith "only atoms can be converted into examples."

let complete_model phi model =
  let open Ast.Gather in
  phi |> free_variables_of_formula |> Variables.to_list
  |> List.map ~f:(fun (id, sort) ->
      match List.Assoc.find ~equal:(=) model id with
      | None -> ((id, sort), None)
      | Some v -> ((id, sort), v))

let rm_undecided map =
  let core_map, ubs =
    List.partition_map map ~f:(function
        | (x, _), Some v -> `Fst(x, v)
        | (x, T_bool.SBool), None -> `Snd(x)
        | (x, T_int.SInt), None -> `Fst(x, T_int.zero Dummy)
        | (x, T_int.SReal), None -> `Fst(x, T_int.mk_real "0." Dummy)
        | _ -> assert false)
  in
  let core_map = Map.Poly.of_alist_exn core_map in
  core_map,
  let bool_true =
    Term.mk_funapp (T_bool.Formula (Formula.mk_atom (Atom.mk_true Dummy) Dummy)) [] Dummy in
  let bool_false =
    Term.mk_funapp (T_bool.Formula (Formula.mk_atom (Atom.mk_false Dummy) Dummy)) [] Dummy in
  ubs
  |> (fun ubs -> if (!Fptprover.Global.config).undecided_bool_expansion
       then Util.List.power (fun x -> [x, bool_true; x, bool_false]) ubs
       else [List.map ~f:(fun x -> x, bool_false) ubs])
  |> List.map ~f:Map.Poly.of_alist_exn

let of_model phi model =
  model
  |> complete_model phi
  |> (fun maps ->
      Fptprover.Debug.print @@
      "new example point:" ^ (maps |> List.map ~f:(fun ((id, _), v) -> id, v) |> str_of_maps);
      maps)
  |> rm_undecided
  |> (fun (core_map, umaps) ->
      let phi = Formula.subst core_map phi |> Logicutil.nnf_of in
      List.rev_map umaps ~f:(fun umap ->
          phi |> Formula.subst umap |> Logicutil.eval_nnf_formula_with_papps))
  |> (fun phis -> Logic.Formula.and_of phis Dummy)
  |> Logic.Formula.cnf_of
  |> List.filter_map ~f:(fun (pos, neg, th_formula) ->
      let pos = List.map pos ~f:example_of_atom |> Set.Poly.of_list in
      let neg = List.map neg ~f:example_of_atom |> Set.Poly.of_list in
      if Logicutil.eval_formula th_formula then None
      else Some {positive = pos; negative = neg})
  |> Set.Poly.of_list

let categorize map model =
  let open Proplogic.Formula in
  (*  Fptprover.Debug.print @@ "model:" ^ (Z3.Model.to_string model); *)
  let tf = model in
  List.fold_left map
    ~init:(Set.Poly.empty, Set.Poly.empty)
    ~f:(fun (pos, neg) (app, prop) ->
        match List.find tf ~f:(fun (prop', _) -> prop = prop') with
        | None -> (pos, neg)
        | Some(_, Some(True _)) -> (Set.Poly.add pos app, neg)
        | Some(_, Some(False _)) -> (pos, Set.Poly.add neg app)
        | _ -> (pos, neg))

let pformula_to_bool = let open Ast.Proplogic.Formula in function False _ -> false | True _ -> true | _ -> failwith "cannot convert into bool."

let rec lookup_model v model = match model with | [] -> None | (key, value)::model -> if key = v then (Some value) else lookup_model v model
let complement_model vars model = List.map ~f:(fun v -> (v, lookup_model v model)) vars
let assess_of edges (var, value) =
  let edge = lookup_model var edges in
  match edge with
  | None -> failwith "fail assess"
  | Some (pedges, nedges) -> List.length (if pformula_to_bool value then pedges else nedges)

let positive_edge_of clauses v = List.filter ~f:(fun clause -> List.mem (Ast.Proplogic.Formula.pos_of_clause clause) v ~equal:(=)) clauses
let negative_edge_of clauses v = List.filter ~f:(fun clause -> List.mem (Ast.Proplogic.Formula.neg_of_clause clause) v ~equal:(=)) clauses

let minimize_core vars clauses model =
  let open Ast.Proplogic in
  let model = List.map ~f:(fun (var, value) -> match value with None -> assert false | Some value -> (var, value)) model in
  let edges = List.map ~f:(fun v -> (v, (positive_edge_of clauses v, negative_edge_of clauses v))) vars in
  let assignments = List.sort ~compare:(fun a b -> compare (assess_of edges b) (assess_of edges a)) model in
  let rec greedy_search remain used not_used =
    match remain with
    | [] -> used
    | remain ->
      match not_used with
      | [] -> used (* failwith "fail to minimize core." *)
      | (var, value)::not_used ->
        let is_solved clause = List.mem (if pformula_to_bool value then Formula.pos_of_clause clause
                                         else Formula.neg_of_clause clause) var ~equal:(=) in
        let remain = List.filter ~f:(fun clause -> not @@ is_solved clause) remain in
        greedy_search remain ((var, value)::used) not_used
  in
  greedy_search clauses [] assignments |> complement_model vars

(* TODO: should merge into minimize_core *)
let minimize_core_for_bSPC abstraction =
  let open Fptprover in
  List.map ~f:(fun residual_solution ->
      Debug.print "******** Dimensionality Reduction";
      Debug.print "residual solution:";
      Debug.print @@ String.concat ~sep:";" @@
      List.map residual_solution ~f:(fun (name, bl) ->
          Printf.sprintf (if bl then "(%s, true)" else "(%s, false)") name);
      let model = Zecchina.SAT.solution_to_model residual_solution in
      let clauses = Zecchina.SAT.formula_of_cnf abstraction in
      let clauses' = Proplogic.Formula.list_of_and clauses in
      let vars = List.concat (List.map clauses'
                                ~f:(fun clause ->
                                    Proplogic.Formula.(pos_of_clause clause @ neg_of_clause clause)))
                 |> List.dedup_and_sort ~compare:(compare) in
      let minimized = minimize_core vars clauses' model in
      minimized
      |> List.fold_left ~f:(fun acc (var, value) ->
          match value with
          | None -> acc
          | Some value -> (Zecchina.SAT.name_of_prop var, Zecchina.SAT.bool_of_prop value)::acc
        ) ~init:[]
      |> (fun minimized ->
          Debug.print "minimized solution:";
          Debug.print @@ String.concat ~sep:";" @@
          List.map minimized ~f:(fun (name, bl) ->
              Printf.sprintf (if bl then "(%s, true)" else "(%s, false)") name);
          minimized)
    )

let str_of_model model =
  let open Ast.Proplogic in
  let aux = function | None -> "*" | Some phi -> Formula.str_of phi in
  List.fold_left ~f:(fun acc (var, value) -> acc ^ (Printf.sprintf "(%s, %s);" (Formula.str_of var) (aux value))) ~init:"" model

(* without retrying to calc satcore *)
let classify _ map (sample:t) =
  let sample = normalize sample in
  let disjs =
    Set.Poly.map sample ~f:(fun clause ->
        let open Proplogic in
        let ps =
          Set.Poly.map ~f:(fun e -> subst_example map e) clause.positive
          |> Set.Poly.to_list
        in
        let ns =
          Set.Poly.map ~f:(fun e ->Formula.mk_neg (subst_example map e) Dummy) clause.negative
          |> Set.Poly.to_list
        in
        Formula.or_of (ps@ns) Proplogic.Dummy)
    |> Set.Poly.to_list
  in
  let phi = Proplogic.Formula.and_of disjs Proplogic.Dummy in
  let open Util in
  Smt.Z3interface.SAT.check_sat phi >>= fun model ->
  let map = map |> Set.Poly.to_list in
  let model =
    if (!Fptprover.Global.config).smart_model then
      begin
        Fptprover.Debug.print "before minimize:";
        Fptprover.Debug.print @@ (str_of_model model) ^ "\n";
        let model = minimize_core (Core.List.map ~f:snd map) disjs model in
        Fptprover.Debug.print "after minimize:";
        Fptprover.Debug.print @@ (str_of_model model) ^ "\n";
        model
      end
    else model
  in
  Some (categorize map model)

let mk_map_for_classification (sample:t) =
  let sample = normalize sample in
  let map = pred_to_prop sample in
  map

let cl_is_in_range range cl =
  let within_range t =
    let geq_ = Formula.mk_atom
        (T_int.mk_geq t (T_int.mk_from_int (-range) Dummy) Dummy) Dummy in
    let leq_ = Formula.mk_atom
        (T_int.mk_leq t (T_int.mk_from_int range Dummy) Dummy) Dummy in
    Formula.mk_and geq_ leq_ Dummy
  in
  let check sample =
    (*    Fptprover.Debug.print ("sample in check:" ^ (str_of_examples ";" sample));*)
    Set.Poly.for_all sample
      ~f:(function
          | True | False -> true
          | PApp (_, args) ->
            List.for_all args ~f:(fun t -> Logicutil.eval_formula (within_range t)))
  in check cl.positive && check cl.negative

let is_in_range range = Set.Poly.for_all ~f:(cl_is_in_range range)

let just_pred_to_prop (sample:t) =
  let all_apps = all_apps_of sample in
  let map = Set.Poly.map all_apps ~f:(fun m -> (m, gen_fresh_prop())) in
  Set.Poly.map sample
    ~f:(fun cl ->
        let ps = Set.Poly.map cl.positive
            ~f:(fun p -> subst_example map p)  in
        let ns = Set.Poly.map cl.negative
            ~f:(fun n -> Proplogic.Formula.mk_neg (subst_example map n) Proplogic.Dummy) in
        Proplogic.Formula.or_of (Set.Poly.union ps ns |> Set.Poly.to_list) Proplogic.Dummy)
  |> Set.Poly.to_list
  |> fun disjs -> Proplogic.Formula.and_of disjs Proplogic.Dummy

let contradict (sample: t) =
  let sample = normalize sample in
  let phi = just_pred_to_prop sample in
  match Smt.Z3interface.SAT.check_sat phi with
  | Some _ -> false
  | None -> true

let print_classified_examples pos neg =
  let open Fptprover in
  let pos =
    pos
    |> Set.Poly.map ~f:(fun p -> PApp p |> str_of_example)
    |> Set.Poly.to_list
    |> String.concat ~sep:","
  in
  let neg =
    neg
    |> Set.Poly.map ~f:(fun n -> PApp n |> str_of_example)
    |> Set.Poly.to_list
    |> String.concat ~sep:","
  in
  Debug.print "after classification:";
  Debug.print @@ "positives:[" ^ pos ^ "]";
  Debug.print @@ "negatives:[" ^ neg ^ "]\n"
