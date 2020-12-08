open Core open Core.Poly
open Logicutil
open Ast.Logic
open Ast
open Fptprover

type t =
  | Formula of Formula.t (* TODO: replace to DCHC format *)
  | WellFounded of Ident.pvar

let rec formula_of = function
  | [] -> Formula.mk_atom (Atom.mk_true Dummy) Dummy
  | (WellFounded _) :: cs -> formula_of cs
  | (Formula phi) :: cs ->
    List.fold_left cs
      ~init:phi
      ~f:(fun acc -> function
          | WellFounded _ -> acc
          | Formula phi ->
            Formula.mk_and acc phi Dummy)

let formula_of_ = function
  | WellFounded _ -> Formula.mk_atom (Atom.mk_true Dummy) Dummy
  | Formula phi -> phi

let string_of_params params =
  let rec aux acc = function
    | [] -> acc
    | (Ident.Tvar ident, _) :: xs -> aux (acc ^ ", " ^ ident) xs
  in
  aux "" params

let variables_of cs = let open Gather in
  List.fold_left cs
    ~init:Variables.empty
    ~f:(fun acc -> function
        | Formula phi -> Variables.union acc (Gather.free_variables_of_formula phi)
        | WellFounded _ -> acc)

let subst maps cs =
  List.map cs ~f:(function
      | Formula phi -> Formula (Formula.subst maps phi)
      | _ as x -> x)

(* TODO : refactoring *)
let subst_ maps = function
  | Formula phi -> Formula (Formula.subst maps phi)
  | _ -> assert false

let string_of = function
  | Formula phi -> Convert.PrinterHum.str_of_formula phi
  | WellFounded (Ident.Pvar ident) ->
    Printf.sprintf "|= WF(%s)" ident

let string_of_constraints =
  List.fold_left ~init:"" ~f:(fun acc c -> acc ^ "\n" ^ string_of c)

let is_valid cs =
  let phi = formula_of cs in
  Debug.print @@ (Convert.PrinterHum.str_of_formula phi);
  Smt.Z3interface.solve [phi]

let make_fresh_params params =
  let rec aux acc = function
    | [] -> acc
    | (_, sort) :: xs ->
      let param = (Ident.mk_fresh_tvar (), sort) in
      aux (param :: acc) xs
  in
  aux [] params

let make_imply phi1 phi2 =
  let open Formula in mk_or (mk_neg phi1 Dummy) phi2 Dummy

(* TODO: remove *_without_parameters in the future *)

(* assuming that variables are alpha renamed. *)
let pn_of_hes (Hes (funcs, entry): Hes.HesLogic.hes) =
  let open Ast.Logic.Formula in
  let rec occurence_in depth flag s_pos s_neg = function
    | Atom (atom, _) ->
      begin
        match atom with
        | True _ | False _ | App ((Psym _), _, _) -> (s_pos, s_neg)
        | App(Var (pvar, _), _, _) ->
          if flag then
            if not @@ Set.Poly.exists s_pos ~f:(fun (pvar', _) -> pvar = pvar') then
              (Set.Poly.add s_pos (pvar, depth), s_neg) else (s_pos, s_neg)
          else if not @@ Set.Poly.exists s_neg ~f:(fun (pvar', _) -> pvar = pvar') then
            (s_pos, Set.Poly.add s_neg (pvar, depth)) else (s_pos, s_neg)
        | _ -> failwith "invalid formula as HES."
      end
    | UnaryOp (Neg, phi, _) -> occurence_in (depth + 1) (not flag) s_pos s_neg phi
    | BinaryOp (And, phi1, phi2, _) ->
      occurence_in (depth + 1) flag s_pos s_neg phi1
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) flag s_pos s_neg phi2)
    | BinaryOp (Or, phi1, phi2, _) ->
      occurence_in (depth + 1) flag s_pos s_neg phi1
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) flag s_pos s_neg phi2)
    | BinaryOp (Imply, phi1, phi2, _) ->
      occurence_in (depth + 1) (not flag) s_pos s_neg phi1
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) flag s_pos s_neg phi2)
    | BinaryOp (Iff, phi1, phi2, _) ->
      occurence_in (depth + 1) flag s_pos s_neg phi1
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) (not flag) s_pos s_neg phi1)
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) flag s_pos s_neg phi2)
      |> (fun (s_pos, s_neg) -> occurence_in (depth + 1) (not flag) s_pos s_neg phi2)
    | Bind _ | LetRec _ -> failwith "bind and letrec has not been supported yet."
  in
  let rec update funcs (s_pos, s_neg) =
    let aux flag (s_pos, s_neg) (pvar, depth) =
      let _, _, _, phi = List.find_exn funcs ~f:(fun (_, pvar', _, _) -> pvar = pvar') in
      occurence_in (depth + 1) flag s_pos s_neg phi in
    let s_pos', s_neg' = Set.Poly.fold s_pos ~init:(s_pos, s_neg) ~f:(aux true) in
    let s_pos', s_neg' = Set.Poly.fold s_neg' ~init:(s_pos', s_neg') ~f:(aux false) in
    if not (Set.Poly.equal s_pos s_pos') || not (Set.Poly.equal s_neg s_neg') then update funcs (s_pos', s_neg')
    else (s_pos', s_neg')
  in occurence_in 0 true Set.Poly.empty Set.Poly.empty entry |> update funcs

let over_approx pvar params phi =
  (*  print_endline "enter@over_approx"; *)
  let pvar' = let Ident.Pvar pid = pvar in Ident.Pvar (pid ^ "_over") in
  let txs, sorts = List.map ~f:(fun (tvar, sort) -> Term.mk_var tvar sort Dummy) params, sorts_of_params params in
  let p1x = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar sorts) txs Dummy) Dummy in
  let _ = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar' sorts) txs Dummy) Dummy in
  (*  print_endline "return@over_approx"; *)
  (pvar, pvar'),
  Formula.mk_or (Formula.mk_neg phi Dummy) p1x Dummy

let under_approx pvar params phi =
  (*  print_endline "enter@under_approx"; *)
  let pvar' = let Ident.Pvar pid = pvar in Ident.Pvar (pid ^ "_under") in
  let txs, sorts = List.map ~f:(fun (tvar, sort) -> Term.mk_var tvar sort Dummy) params, sorts_of_params params in
  let p1x = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar sorts) txs Dummy) Dummy in
  let _ = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar' sorts) txs Dummy) Dummy in
  (*  print_endline "return@under_approx"; *)
  (pvar, pvar'),
  Formula.mk_or (Formula.mk_neg p1x Dummy) phi Dummy

(* pos = true => under approximation *)
let mk_wf_cnst pos pvar params =
  let wp = Ident.mk_fresh_pvar () in
  let txs, sorts = List.map ~f:(fun (tvar, sort) -> Term.mk_var tvar sort Dummy) params,
                   sorts_of_params params in
  let ys = make_fresh_params params in
  let tys = List.map ~f:(fun (tvar, sort) -> Term.mk_var tvar sort Dummy) ys in
  let q1y = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar sorts) tys Dummy) Dummy in
  let q2xy = Formula.mk_atom (Atom.mk_app (Predicate.mk_var wp (sorts@sorts)) (txs @ tys) Dummy) Dummy in
  let phi = if pos then Formula.mk_and q1y q2xy Dummy else Formula.mk_or q1y (Formula.mk_neg q2xy Dummy) Dummy in
  let wp_map = Formula.subst_pred pvar ys phi in
  params, wp_map, WellFounded wp

let rec extend_phi exenv = let open Logic.Formula in
  function
  | Atom (atom, info) as phi ->
    begin
      match atom with
      | True _ | False _ | App (Psym _, _, _) -> Atom (atom, info)
      | App (Var (pvar', sorts), terms, info'') ->
        begin
          match Map.Poly.find exenv pvar' with
          | None -> phi
          | Some params ->
            let txs, sxs = List.unzip (List.map params ~f:(fun (tvar, sort) -> Term.mk_var tvar sort Dummy, sort)) in
            Atom (App(Var(pvar', sxs@sorts), (txs@terms), info''), info)
        end
      | _ -> failwith @@ Printf.sprintf "invalid atom@extend_phi: %s" (Convert.PrinterHum.str_of_atom atom)
    end
  | UnaryOp (Neg, phi, info) -> UnaryOp (Neg, extend_phi exenv phi, info)
  | BinaryOp (op, phi1, phi2, info) -> BinaryOp(op, extend_phi exenv phi1, extend_phi exenv phi2, info)
  | phi -> failwith @@ Printf.sprintf "Invalid formula @ extend_phi: %s" (Convert.PrinterHum.str_of_formula phi)

let print_s at s =
  Printf.printf "s@%s: [%s]\n" at
    (String.concat ~sep:";" @@
     Set.Poly.to_list @@ Set.Poly.map ~f:(fun (Ident.Pvar pid) -> pid) s)

let mk_lfpp_constraint acc_cnst map (rest: Hes.HesLogic.func list) exenv pvar params phi =
  (* embed wf_predicate *)
  let _, (wp_map: Formula.t -> 'a), wf_cnst = mk_wf_cnst true pvar params in
  let rest = List.map ~f:(fun (fp, pvar, params, phi) -> (fp, pvar, params, (wp_map phi))) rest in
  let phi = wp_map phi in
  (* generate constraints *)
  let (map_a, map_b), approx_cnst = under_approx pvar params phi in
  (* extend parameters *)
  let approx_cnst = extend_phi exenv approx_cnst in
  let map = Map.Poly.add_exn map ~key:map_a ~data:map_b in
  (Formula approx_cnst)::(wf_cnst)::acc_cnst, map, rest

let mk_lfpn_constraint acc_cnst map rest exenv pvar params phi =
  (*  print_endline "enter@mk_lfpn_constarint";*)
  let (map_a, map_b), approx_cnst = over_approx pvar params phi in
  let map = Map.Poly.add_exn map ~key:map_a ~data:map_b in
  (* extend parameters *)
  let approx_cnst = extend_phi exenv approx_cnst in
  (Formula approx_cnst)::acc_cnst, map, rest

let mk_gfpp_constraint acc_cnst map rest exenv pvar params phi =
  (*  print_endline "enter@mk_gfpp_constarint";*)
  let (map_a, map_b), approx_cnst = under_approx pvar params phi in
  let map = Map.Poly.add_exn map ~key:map_a ~data:map_b in
  (* extend parameters *)
  let approx_cnst = extend_phi exenv approx_cnst in
  (Formula approx_cnst)::acc_cnst, map, rest

let mk_gfpn_constraint acc_cnst map rest exenv pvar params phi =
  (*  print_endline "enter@mk_gfpn_constraint";*)
  (* embed wf_predicate *)
  let _, (wp_map: Formula.t -> 'a), wf_cnst = mk_wf_cnst false pvar params in
  let rest = List.map ~f:(fun (fp, pvar, params, phi) -> (fp, pvar, params, (wp_map phi))) rest in
  let phi = wp_map phi in
  (* generate constraints *)
  let (map_a, map_b), approx_cnst = over_approx pvar params phi in
  (* extend parameters *)
  let approx_cnst = extend_phi exenv approx_cnst in
  let map = Map.Poly.add_exn map ~key:map_a ~data:map_b in
  (*  let map = match Map.Poly.append ~upper_part:map ~lower_part:map' with `Ok map -> map | _ -> map' in *)
  (Formula approx_cnst)::(wf_cnst)::acc_cnst, map, rest

let cmp deplist (p1, pos1) (p2, pos2) =
  let rec deps_of acc p =
    match List.find_exn deplist ~f:(fun (p', _) -> p = p') with
    | _, [] -> acc
    | _, deps -> List.fold_left ~f:(fun acc d -> deps_of acc d) ~init:acc deps
  in
  if pos1 <> pos2 then 0
  else
    let deps1, deps2 = deps_of [] p1, deps_of [] p2 in
    if List.mem deps1 p2 ~equal:(=) then 1
    else if List.mem deps2 p1 ~equal:(=) then -1 else 0

let mk_dep_list func pvars =
  let aux (pvar, _) =
    let _, _, _, phi = List.find_exn ~f:(fun (_, pvar', _, _) -> pvar = pvar') func in
    let rec inner =
      let open Ast.Logic.Formula in
      function
      | Atom (atom, _) ->
        begin
          match atom with
          | True _ | False _ | App ((Psym _), _, _) -> []
          | App(Var (pvar, _), _, _) -> [pvar]
          | _ -> failwith "invalid formula as HES."
        end
      | UnaryOp (Neg, phi, _) -> inner phi
      | BinaryOp ((And | Or), phi1, phi2, _) -> (inner phi1) @ (inner phi2)
      | phi -> failwith @@ Printf.sprintf "%s is not supported." (Convert.PrinterHum.str_of_formula phi)
    in (pvar, inner phi)
  in
  List.map ~f:aux pvars

let pvars_to_eqs func s =
  let lookup_func pvar = List.find_exn ~f:(fun (_, pvar', _, _) -> pvar = pvar') func in
  let sl = Set.Poly.to_list s in
  List.sort ~compare:(fun (_, d1) (_, d2) -> compare d1 d2) sl
  |> List.map ~f:(fun (pvar, _) -> lookup_func pvar)

let update_cnst (map: (Ident.pvar, Ident.pvar) Map.Poly.t) =
  List.map ~f:(function WellFounded _ as c -> c
                      | Formula phi -> Formula (Formula.rename_preds map phi))

let mk_dep_graph eqs =
  let neighbors_of nodes pvar =
    Set.Poly.find_exn nodes ~f:(fun (pvar', _) -> pvar = pvar') |> (fun (_, neighbors) -> neighbors) in
  let calc_reachable pvar nodes =
    let init_n = neighbors_of nodes pvar in
    let rec inner neighbors =
      let neighbors' = Set.Poly.fold
          ~f:(fun acc pvar' ->
              if pvar = pvar' then acc else
                Set.Poly.union (neighbors_of nodes pvar') acc)
          (*                             Set.Poly.diff (Set.Poly.union (neighbors_of nodes pvar') acc) (Set.Poly.singleton pvar)) *)
          ~init:neighbors neighbors in
      if Set.Poly.equal neighbors neighbors' then neighbors' else inner neighbors'
    in inner init_n
  in
  let nodes = List.map eqs ~f:(fun (_, pvar, _, phi) -> (pvar, Formula.get_fpv phi)) |> Set.Poly.of_list in
  Set.Poly.map ~f:(fun (pvar, _) -> (pvar, calc_reachable pvar nodes)) nodes

let reachable_from wenv pvar graph =
  let weight_of_exn wenv pvar = Map.Poly.find_exn wenv pvar in
  let wpvar = weight_of_exn wenv pvar in
  let (_, reachable) = Set.Poly.find_exn graph ~f:(fun (pvar', _) -> pvar = pvar') in
  Set.Poly.filter reachable ~f:(fun pvar' -> weight_of_exn wenv pvar' > wpvar)

let reachable_to target_pvar graph pvars =
  Set.Poly.filter pvars ~f:(fun pvar ->
      let (_, neighbors) = Set.Poly.find_exn ~f:(fun (pvar', _) -> pvar = pvar') graph in
      Set.Poly.exists ~f:(fun pvar' -> pvar' = target_pvar) neighbors
    )

let mk_ext_env pos dep_graph wenv eq =
  let update_env acc pvar xs =
    Map.Poly.update acc pvar ~f:(function None -> xs | Some xs' -> xs@xs') in
  let aux acc (fp, pvar, params, _) =
    let s = reachable_from wenv pvar dep_graph |> reachable_to pvar dep_graph in
    let s = Set.Poly.diff s (Set.Poly.singleton pvar) in
    match fp, pos with
    | Predicate.Mu, `Pos | Predicate.Nu, `Neg ->
      Set.Poly.fold s ~init:acc ~f:(fun acc' pvar -> update_env acc' pvar params)
    | _ -> acc
  in
  List.fold_left eq ~f:aux ~init:Map.Poly.empty

let mk_wenv pos =
  Set.Poly.fold ~f:(fun acc (pvar, w) -> Map.Poly.add_exn acc ~key:pvar ~data:w) ~init:Map.Poly.empty pos

let str_of_node (Ident.Pvar pid, neighbors) =
  Printf.sprintf "(%s, [%s])" pid (String.concat ~sep:"," @@
                                   Set.Poly.to_list @@ Set.Poly.map ~f:(fun (Ident.Pvar pid) -> pid) neighbors)

let str_of_graph graph =
  String.concat ~sep:"\n" @@ Set.Poly.to_list @@ Set.Poly.map graph ~f:(str_of_node)

let str_of_exenv exenv =
  let aux ((Ident.Pvar pid), args) =
    Printf.sprintf "(%s, [%s])" pid (String.concat ~sep:"," @@ List.map ~f:(fun ((Ident.Tvar tid), _) -> tid) args) in
  Map.Poly.to_alist exenv
  |> List.map ~f:aux
  |> String.concat ~sep:";"

let str_of_wenv wenv =
  String.concat ~sep:";" @@
  List.map ~f:(fun (Ident.Pvar pid, d) -> Printf.sprintf "(%s, %d)" pid d) @@ Map.Poly.to_alist wenv

let extract (Hes.HesLogic.Hes (func, entry) as hes) =
  Debug.print "=-=-=-=-=- pCSP generation -=-=-=-=-=";
  let (s_pos, s_neg) = pn_of_hes hes in
  let (pwenv, nwenv) = mk_wenv s_pos, mk_wenv s_neg in
  Debug.print "******* weight";
  Debug.print @@ "In positive: [" ^ str_of_wenv pwenv ^ "]";
  Debug.print @@ "In negative: [" ^ str_of_wenv nwenv ^ "]";
  let (eq_pos, eq_neg) = (pvars_to_eqs func s_pos), (pvars_to_eqs func s_neg) in
  let (dep_graph_pos, dep_graph_neg) = mk_dep_graph eq_pos, mk_dep_graph eq_neg in
  Debug.print "******* analyze dependency";
  Debug.print @@ "In positive: [" ^ (str_of_graph dep_graph_pos) ^ "]";
  Debug.print @@ "In negative: [" ^ (str_of_graph dep_graph_neg) ^ "]";
  let pexenv = mk_ext_env `Pos dep_graph_pos pwenv eq_pos in
  let nexenv = mk_ext_env `Neg dep_graph_neg nwenv eq_neg in
  Debug.print "******* generate environment for parameter extension";
  Debug.print @@ "In positive: [" ^ (str_of_exenv pexenv) ^ "]";
  Debug.print @@ "In negative: [" ^ (str_of_exenv nexenv) ^ "]";
  let rec inner exenv pos cnst (map: (Ident.pvar, Ident.pvar) Map.Poly.t) = function
    | [] -> update_cnst map cnst
    | (fp, pvar, params, phi)::rest ->
      let generator = match fp, pos with
        | Predicate.Mu, true  -> mk_lfpp_constraint | Predicate.Mu, false -> mk_lfpn_constraint
        | Predicate.Nu, true  -> mk_gfpp_constraint | Predicate.Nu, false -> mk_gfpn_constraint
      in
      let cnst, map, rest_eqs = generator cnst map rest exenv pvar params phi in
      inner exenv pos cnst map rest_eqs
  in inner nexenv false
    (inner pexenv true [Formula entry] Map.Poly.empty eq_pos) Map.Poly.empty eq_neg

(* if a constraint has variables that appear in other constraint, rename it *)
let rec make_constraints_independent used acc = function
  | [] -> acc
  | (Formula phi) :: cs ->
    let free_vars = Gather.free_variables_of_formula phi in
    let to_be_freshed = Gather.Variables.inter free_vars used in
    let maps =
      List.map (Gather.Variables.to_list to_be_freshed)
        ~f:(fun (Ident.Tvar ident, sort) ->
            let new_ident = Ident.Tvar ("#" ^ ident) in
            (Ident.Tvar ident, Term.mk_var new_ident sort Dummy)
          )
      |> Map.Poly.of_alist_exn in
    let new_used =
      Gather.Variables.map to_be_freshed
        ~f:(fun (Ident.Tvar ident, sort) ->
            let new_ident = "#" ^ ident in
            (Ident.Tvar new_ident, sort)
          ) in
    let phi = Formula.subst maps phi in
    let used = Gather.Variables.union free_vars used in
    let used = Gather.Variables.union new_used used in
    make_constraints_independent used (Formula phi :: acc) cs
  | (WellFounded pvar) :: cs ->
    make_constraints_independent used ((WellFounded pvar)::acc) cs
(* TODO *)

let extract hes = extract hes

(* TODO : convert constraints into CNF *)
(* let extract_locally _ = assert false (*extract phi*) (* stub *) *)

let pred_free_variables_of = function
  | Formula phi -> Gather.pred_free_variables_of_formula phi
  | WellFounded _ -> Gather.PredVariables.empty

let subst_pred c (pvar, params, phi) =
  match c with
  | Formula phi' ->
    let phi = Formula.subst_pred pvar params phi phi' in
    Formula phi
  | WellFounded _ as x -> x

let subst_pred_ c ((pvar, params), phi) =
  subst_pred c (pvar, params, phi)

let subst_pred cs penv =
  List.map cs ~f:(fun c -> subst_pred c penv)

let wf_constraints_in cs =
  List.filter cs ~f:(function WellFounded _ -> true | _ -> false)

let subst_cs_with_preds cs penvs =
  List.fold_left penvs ~init:cs ~f:subst_pred


(* attributes *)
let number_of_pvars cs =
  let open Gather in
  let pvars =
    List.fold_left
      ~init:PredVariables.empty
      ~f:(fun acc -> function
          | WellFounded _ -> acc
          | Formula phi ->
            PredVariables.union
              acc
              (pred_free_variables_of_formula phi)
        ) cs in
  Set.length pvars

let arities cs =
  let open Gather in
  let pvars =
    List.fold_left
      ~init:PredVariables.empty
      ~f:(fun acc -> function
          | WellFounded _ -> acc
          | Formula phi ->
            PredVariables.union
              acc
              (pred_free_variables_of_formula phi)
        ) cs in
  let ars =
    List.map ~f:(fun (_, sorts) -> List.length sorts) (Set.to_list pvars)
  in ars

let pred_free_vars_of_cs cs =
  let open Gather in
  List.fold_left cs
    ~init:PredVariables.empty
    ~f:(fun acc c -> PredVariables.union
           acc
           (pred_free_variables_of c))
  |> PredVariables.to_list

let let_formula =function
  | Formula f -> f
  | WellFounded _ -> assert false


let is_well_founded (cs : t list) pvar =
  List.exists cs ~f:(function WellFounded pvar' -> pvar = pvar' | _ -> false)

let pinfo_and_formula (cs : t list) =
  let pvars = pred_free_vars_of_cs cs in
  let pinfo = List.map pvars
      ~f:(fun (pvar, params) ->
          (pvar, params, is_well_founded cs pvar))
  in
  let formulas = List.fold_left
      ~f:(fun acc -> function
          | WellFounded _ -> acc
          | Formula phi -> phi::acc) ~init:[] cs
  in (pinfo, formulas)
