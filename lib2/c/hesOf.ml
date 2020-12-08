open Linked
open CSyntax
open Ast
open Ast.Logic
open Hes
open Fptprover
open Optimizer

exception Error of string

let fresh_pvar env phi =
  let pvarname =
    if Ctl.is_af phi then "AF"
    else if Ctl.is_ef phi then "EF"
    else if Ctl.is_ag phi then "AG"
    else if Ctl.is_eg phi then "EG"
    else if Ctl.is_or phi then "OR"
    else if Ctl.is_and phi then "AND"
    else if Ctl.is_imp phi then "IMP"
    else if Ctl.is_ap phi then raise (Error "AP must be wrapped by others")
    else assert false
  in
  let id = List.fold_left
      (fun id (_, _, pvar) ->
         if Core.String.is_prefix (Ident.name_of_pvar pvar) ~prefix: pvarname then
           id+1
         else
           id
      ) 1 env
  in
  Ident.Pvar (pvarname ^ (string_of_int id))

let get_funinfo prev_env env phi stmt =
  (* TODO: improve performance *)
  let phifv = Ctl.get_fv phi in
  let rgenv = ReadGraph.get_rgenv phifv prev_env stmt in
  let state =
    Variables.union
      phifv
      (
        ReadGraph.rgenv_entries rgenv
        |> List.filter
          (fun (_, rg) -> ReadGraph.rg_get stmt rg |> ReadGraph.length > 0)
        |> List.map
          (fun (tvar, _) -> Ident.name_of_tvar tvar)
        |> Variables.of_list
      )
    |> State.of_variables
  in
  let pvar_opt =
    List.find_opt
      (fun (phi', stmt', _) -> phi == phi' && stmt == stmt')
      env
  in
  let env, pvar =
    match pvar_opt with
    | None ->
      let pvar = fresh_pvar env phi in
      (phi, stmt, pvar) :: env, pvar
    | Some (_, _, pvar) -> env, pvar
  in
  env, pvar, state

let rec formula_of_phi prev_env env phi stmt =
  match Ctl.unwrap phi with
  | Ctl.PHI _ ->
    let env, pvar', state' = get_funinfo prev_env env phi stmt in
    env, State.appformula_of pvar' state'
  | Ctl.PHI2 _ ->
    let binop, phi1, phi2 = Ctl.let_binop phi in
    let env, fml1 = formula_of_phi prev_env env phi1 stmt in
    let env, fml2 = formula_of_phi prev_env env phi2 stmt in
    env,
    Formula.mk_binop binop fml1 fml2 Dummy
  | Ctl.FORMULA fml ->
    env, fml

let next_formula_of_phi prev_env env phi stmt =
  formula_of_phi prev_env env (Ctl.let_unop phi) stmt

let hesfunc_of_c_one prev_env env phi stmt =
  let env, pvar, state = get_funinfo prev_env env phi stmt in
  let env, body =
    if LinkedStatement.is_assign stmt then
      let varname, term, nxt_stmt = LinkedStatement.let_assign stmt in
      let env, pvar', state' = get_funinfo prev_env env phi !nxt_stmt in
      let state' = State.update varname term state' in
      env, State.appformula_of pvar' state'
    else if LinkedStatement.is_nondet_assign stmt then
      let varname, nxt_stmt = LinkedStatement.let_nondet_assign stmt in
      let env, pvar', state' = get_funinfo prev_env env phi !nxt_stmt in
      let binder =
        if Ctl.is_a phi then Formula.Forall
        else Formula.Exists
      in
      env,
      Formula.mk_bind binder
        [(Ident.Tvar varname, T_int.SInt)]
        (State.appformula_of pvar' state') Dummy
    else if LinkedStatement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = LinkedStatement.let_if stmt in
      let env, t_pvar, t_state = get_funinfo prev_env env phi !t_stmt in
      let env, f_pvar, f_state = get_funinfo prev_env env phi !f_stmt in
      let t_fml = State.appformula_of t_pvar t_state in
      let f_fml = State.appformula_of f_pvar f_state in
      env,
      Formula.mk_and
        (Formula.mk_imply cond_fml t_fml Dummy)
        (Formula.mk_imply (Formula.mk_neg cond_fml Dummy) f_fml Dummy)
        Dummy
    else if LinkedStatement.is_nondet stmt then
      let stmt1, stmt2 = LinkedStatement.let_nondet stmt in
      let env, pvar1, state1 = get_funinfo prev_env env phi !stmt1 in
      let env, pvar2, state2 = get_funinfo prev_env env phi !stmt2 in
      let fml1 = State.appformula_of pvar1 state1 in
      let fml2 = State.appformula_of pvar2 state2 in
      let binop =
        if Ctl.is_a phi then Formula.And
        else Formula.Or
      in
      env,
      Formula.mk_binop binop fml1 fml2 Dummy
    else if LinkedStatement.is_assume stmt then
      let assume_fml, nxt_stmt = LinkedStatement.let_assume stmt in
      let env, pvar, state = get_funinfo prev_env env phi !nxt_stmt in
      let fml = State.appformula_of pvar state in
      let binop =
        if Ctl.is_a phi then
          Formula.Imply
        else
          Formula.And
      in
      env,
      Formula.mk_binop binop assume_fml fml Dummy
    else if LinkedStatement.is_exit stmt then
      let atom =
        if Ctl.is_f phi then Atom.mk_false Dummy
        else if Ctl.is_g phi then Atom.mk_true Dummy
        else assert false
      in
      env, Formula.mk_atom atom Dummy
    else if LinkedStatement.is_nop stmt then
      let nxt_stmt = LinkedStatement.let_nop stmt in
      let env, pvar, state = get_funinfo prev_env env phi !nxt_stmt in
      let fml = State.appformula_of pvar state in
      env, fml
    else
      raise (Error "unknown stmt")
  in
  let env, fml = next_formula_of_phi prev_env env phi stmt in
  let body =
    let binop =
      if Ctl.is_f phi then Formula.Or
      else if Ctl.is_g phi then Formula.And
      else assert false
    in
    Formula.mk_binop binop fml body Dummy
  in
  let bounds = State.bounds_of state in
  let fix =
    if Ctl.is_f phi then Predicate.Mu
    else if Ctl.is_g phi then Predicate.Nu
    else assert false
  in
  env, HesLogic.mk_func fix pvar bounds body

let rec hes_of_c_rep_stmt prev_env (env, funcs_rev) phi stmt =
  let env, pvar, _ = get_funinfo prev_env env phi stmt in
  let exists =
    List.exists
      (fun func ->
         let _, pvar', _, _ = HesLogic.let_function func in
         pvar = pvar'
      )
      funcs_rev
  in
  if exists then
    env, funcs_rev
  else
    let env, func = hesfunc_of_c_one prev_env env phi stmt in
    let funcs_rev = func :: funcs_rev in
    LinkedStatement.get_next_statements stmt
    |> List.fold_left
      (fun (env, funcs_rev) nxt_stmt ->
         hes_of_c_rep_stmt prev_env (env, funcs_rev) phi nxt_stmt
      )
      (env, funcs_rev)

let rec get_next_phis ?(res=[]) phi =
  match Ctl.unwrap phi with
  | PHI _ -> phi :: res
  | PHI2 (phi1, phi2) ->
    get_next_phis ~res:(get_next_phis ~res phi1) phi2
  | FORMULA _ -> res

let rec hes_of_c_rep_phi prev_env (env, funcs_rev) phi stmt =
  let dispose_next_phis phi (env, funcs_rev) =
    get_next_phis phi
    |> List.fold_left
      (fun (env, funcs_rev) phi' ->
         hes_of_c_rep_phi prev_env (env, funcs_rev) phi' stmt
      )
      (env, funcs_rev)
  in
  if Ctl.is_unop phi then
    let env, funcs_rev = hes_of_c_rep_stmt prev_env (env, funcs_rev) phi stmt in
    dispose_next_phis (Ctl.let_unop phi) (env, funcs_rev)
  else (
    assert(Ctl.is_binop phi);
    let env, funcs_rev = dispose_next_phis phi (env, funcs_rev) in
    let env, fml = formula_of_phi prev_env env phi stmt in
    let env, pvar, state = get_funinfo prev_env env phi stmt in
    let func = HesLogic.mk_func Predicate.Nu pvar (State.bounds_of state) fml in
    let funcs_rev = funcs_rev @ [func] in
    env, funcs_rev
  )

let entry_of_c prev_env env (phi, _, inits, stmt) =
  let env, pvar, state = get_funinfo prev_env env phi stmt in
  let state = List.fold_left Init.update_state state inits in
  let fml = State.appformula_of pvar state in
  let fml = List.fold_left Init.update_formula_A fml inits in
  let bounds =
    Formula.get_ftv fml
    |> Core.Set.Poly.to_list
    |> List.map (fun tvar -> tvar, T_int.SInt)
  in
  let binder =
    if Ctl.is_e phi then
      Formula.Exists
    else
      Formula.Forall
  in
  env,
  Formula.mk_bind_if_bounded binder bounds fml Dummy

let hes_of_cctl (phi, decls, inits, stmt) =
  let stmt = LinkedStatement.of_statement stmt in
  Debug.print @@ "vvvvvvvvvvvvv Linked C vvvvvvvvvvvvv";
  Debug.print @@ LinkedStatement.string_of stmt;
  Debug.print "";
  let _, decls, inits, stmt = Optimizer.optimize (Ctl.get_fv phi) decls inits stmt in
  Debug.print @@ "vvvvvvvvvvvvv Optimized Linked C vvvvvvvvvvvvv";
  Debug.print @@ LinkedStatement.string_of stmt;
  Debug.print "";
  let prev_env = Util.get_prev_env stmt in
  let env, funcs = hes_of_c_rep_phi prev_env ([], []) phi stmt in
  let _, entry = entry_of_c prev_env env (phi, decls, inits, stmt) in
  let funcs = List.rev funcs in
  HesLogic.mk_hes funcs entry

let hes_of_chmes (hmes, decls, inits, entry_stmt) =
  let entry_stmt = LinkedStatement.of_statement entry_stmt in
  Debug.print @@ "vvvvvvvvvvvvv Linked C vvvvvvvvvvvvv";
  Debug.print @@ LinkedStatement.string_of entry_stmt;
  Debug.print "";
  let hmes_fv = HMES.get_ftv hmes in
  let _, _, inits, entry_stmt = Optimizer.optimize hmes_fv decls inits entry_stmt in
  Debug.print @@ "vvvvvvvvvvvvv Optimized Linked C vvvvvvvvvvvvv";
  Debug.print @@ LinkedStatement.string_of entry_stmt;
  Debug.print "";
  let prev_env = Util.get_prev_env entry_stmt in
  let stmts = LinkedStatement.get_all_statements entry_stmt in
  (* make a table for stmt -> id *)
  let stmt_to_id = LinkedStatementHashtbl.create 1234 in
  List.iteri (fun idx stmt -> LinkedStatementHashtbl.add stmt_to_id stmt idx) stmts;
  let id_of_stmt stmt = LinkedStatementHashtbl.find stmt_to_id stmt in
  let pvar_of stmt hmes_pvar =
    Ident.Pvar (Printf.sprintf "L%d%s" (id_of_stmt stmt + 1) (Ident.name_of_pvar hmes_pvar))
  in
  let state_of stmt =
    let rgenv = ReadGraph.get_rgenv hmes_fv prev_env stmt in
    Variables.union
      hmes_fv
      (
        ReadGraph.rgenv_entries rgenv
        |> List.filter
          (fun (_, rg) -> ReadGraph.rg_get stmt rg |> ReadGraph.length > 0)
        |> List.map
          (fun (tvar, _) -> Ident.name_of_tvar tvar)
        |> Variables.of_list
      )
    |> State.of_variables
  in
  let hmes_funcs, entry_pvar = HMES.let_hmes hmes in
  let formula_of_dia stmt hmes_pvar =
    if LinkedStatement.is_assign stmt then
      let var_name, term, nxt_stmt = LinkedStatement.let_assign stmt in
      let state = state_of !nxt_stmt |> State.update var_name term in
      let pvar = pvar_of !nxt_stmt hmes_pvar in
      State.appformula_of pvar state
    else if LinkedStatement.is_assume stmt then
      let fml, nxt_stmt = LinkedStatement.let_assume stmt in
      let pvar = pvar_of !nxt_stmt hmes_pvar in
      let state = state_of !nxt_stmt in
      Formula.mk_and fml (State.appformula_of pvar state) Dummy
    else if LinkedStatement.is_exit stmt then
      (* todo? *)
      let pvar = pvar_of stmt hmes_pvar in
      let state = state_of stmt in (* empty state *)
      State.appformula_of pvar state
    else if LinkedStatement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = LinkedStatement.let_if stmt in
      let t_fml = State.appformula_of (pvar_of !t_stmt hmes_pvar) (state_of !t_stmt) in
      let f_fml = State.appformula_of (pvar_of !f_stmt hmes_pvar) (state_of !f_stmt) in
      Formula.mk_and
        (Formula.mk_imply cond_fml t_fml Dummy)
        (Formula.mk_imply (Formula.mk_neg cond_fml Dummy) f_fml Dummy)
        Dummy
    else if LinkedStatement.is_nondet stmt then
      let nxt_stmt1, nxt_stmt2 = LinkedStatement.let_nondet stmt in
      Formula.mk_or
        (State.appformula_of (pvar_of !nxt_stmt1 hmes_pvar) (state_of !nxt_stmt1))
        (State.appformula_of (pvar_of !nxt_stmt2 hmes_pvar) (state_of !nxt_stmt2))
        Dummy
    else if LinkedStatement.is_nondet_assign stmt then
      let var_name, nxt_stmt = LinkedStatement.let_nondet_assign stmt in
      let state = state_of !nxt_stmt in
      let body = State.appformula_of (pvar_of !nxt_stmt hmes_pvar) state in
      if State.mem var_name state then
        Formula.mk_exists
          [Ident.Tvar var_name, T_int.SInt]
          body
          Dummy
      else
        body
    else if LinkedStatement.is_nop stmt then
      let nxt_stmt = LinkedStatement.let_nop stmt in
      let pvar = pvar_of !nxt_stmt hmes_pvar in
      State.appformula_of pvar (state_of !nxt_stmt)
    else
      failwith "not implemented"
  in
  let atom_of hmes_atom =
    if HMESAtom.is_true hmes_atom || HMESAtom.is_false hmes_atom || HMESAtom.is_predapp hmes_atom then
      HMESAtom.atom_of hmes_atom
    else if HMESAtom.is_pvar hmes_atom then
      failwith "not implemented"
    else
      failwith "not implemented"
  in
  let rec formula_of stmt hmes_pvar hmes_fml =
    if HMESFormula.is_and hmes_fml then
      let hmes_fml1, hmes_fml2 = HMESFormula.let_and hmes_fml in
      Formula.mk_and (formula_of stmt hmes_pvar hmes_fml1) (formula_of stmt hmes_pvar hmes_fml2) Dummy
    else if HMESFormula.is_or hmes_fml then
      let hmes_fml1, hmes_fml2 = HMESFormula.let_or hmes_fml in
      Formula.mk_or (formula_of stmt hmes_pvar hmes_fml1) (formula_of stmt hmes_pvar hmes_fml2) Dummy
    else if HMESFormula.is_box hmes_fml then
      failwith "not implemented"
    else if HMESFormula.is_dia hmes_fml then
      let hmes_fml' = HMESFormula.let_dia hmes_fml in
      (* todo *)
      let atom = HMESFormula.let_atom hmes_fml' in
      let pvar = HMESAtom.let_pvar atom in
      formula_of_dia stmt pvar
    else if HMESFormula.is_atom hmes_fml then
      let atom = HMESFormula.let_atom hmes_fml in
      Formula.mk_atom (atom_of atom) Dummy
    else
      failwith "not implemented"
  in
  let hes_funcs =
    List.fold_left
      (fun hes_funcs (fix, pvar, hmes_fml) ->
         List.fold_left
           (fun hes_funcs stmt ->
              let pvar' = pvar_of stmt pvar in
              let state = state_of stmt in
              let bounds = State.bounds_of state in
              let fml = formula_of stmt pvar hmes_fml in
              HesLogic.mk_func fix pvar' bounds fml
              :: hes_funcs
           ) hes_funcs stmts
      ) [] hmes_funcs
    |> List.rev
  in
  let entry =
    let pvar = pvar_of entry_stmt entry_pvar in
    let state = state_of entry_stmt in
    let state = List.fold_left Init.update_state state inits in
    let fml = State.appformula_of pvar state in
    let fml = List.fold_left Init.update_formula_E fml inits in
    Convert.FormulaConverter.elim_fv_with_exists fml
  in
  let hes_neg = HesLogic.mk_hes hes_funcs entry in
  Debug.print @@ "vvvvvvvvvvvvv Converted Hes (neg) vvvvvvvvvvvvv";
  Debug.print @@ Convert.Hesutil.str_of_hes hes_neg;
  Debug.print "";
  Convert.Hesutil.get_dual_hes hes_neg
