open Ast
open Ast.Logic

let elim_fv_with_binder binder fml =
  let fv = Formula.get_ftv fml |> Core.Set.Poly.to_list in
  (* TODO: infer the sorts *)
  let bounds = List.map (fun tvar -> tvar, T_int.SInt) fv in
  Formula.mk_bind_if_bounded binder bounds fml Dummy

let elim_fv_with_exists fml = elim_fv_with_binder Formula.Exists fml
let elim_fv_with_forall fml = elim_fv_with_binder Formula.Forall fml

let move_quantifiers_to_front fml =
  let rec rename_in_formula used_names replace_env fml =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      let atom = rename_in_atom replace_env atom in
      Formula.mk_atom atom info, used_names, replace_env
    else if Formula.is_binop fml then
      let binop, left, right, info = Formula.let_binop fml in
      let left, used_names, replace_env = rename_in_formula used_names replace_env left in
      let right, used_names, replace_env = rename_in_formula used_names replace_env right in
      Formula.mk_binop binop left right info, used_names, replace_env
    else if Formula.is_unop fml then
      let unop, body, info = Formula.let_unop fml in
      let body, used_names, replace_env = rename_in_formula used_names replace_env body in
      Formula.mk_unop unop body info, used_names, replace_env
    else if Formula.is_bind fml then
      let binder, bounds, body, info = Formula.let_bind fml in
      let new_bounds = List.map
          (fun (tvar, sort) ->
             let var_name = ref (Ident.name_of_tvar tvar ^ "!q") in
             while Env.has !var_name used_names do
               var_name := !var_name ^ "!"
             done;
             Ident.Tvar !var_name, sort
          )
          bounds
      in
      let new_bound_tvars, _ = Core.List.unzip new_bounds in
      let bound_tvars, _ = Core.List.unzip bounds in
      let used_names = Env.update (List.map (fun tvar -> Ident.name_of_tvar tvar, ()) bound_tvars) used_names in
      let replace_env = Env.update (Core.List.zip_exn bound_tvars new_bound_tvars) replace_env in
      let body, used_names, replace_env = rename_in_formula used_names replace_env body in
      Formula.mk_bind binder new_bounds body info, used_names, replace_env
    else
      assert false
  and rename_in_atom replace_env atom =
    if Atom.is_true atom || Atom.is_false atom then
      atom
    else if Atom.is_app atom then
      let pred, args, info = Atom.let_app atom in
      let pred = rename_in_predicate pred in
      let args = List.map (rename_in_term replace_env) args in
      Atom.mk_app pred args info
    else
      assert false
  and rename_in_predicate pred =
    if Predicate.is_fix pred then
      let fix, pvar, args, body = Predicate.let_fix pred in
      let body = rename body in
      Predicate.mk_fix fix pvar args body
    else if Predicate.is_psym pred || Predicate.is_var pred then
      pred
    else
      assert false
  and rename_in_term replace_env term =
    if Term.is_var term then
      let tvar, sort, info = Term.let_var term in
      Term.mk_var (Env.lookup tvar replace_env) sort info
    else if Term.is_funapp term then
      let funsym, args, info = Term.let_funapp term in
      Term.mk_funapp funsym (List.map (rename_in_term replace_env) args) info
    else
      assert false
  and rename fml =
    let fv = Formula.get_ftv fml |> Core.Set.Poly.to_list in
    (* let fv_names = Env.update (List.map (fun tvar -> (Ident.name_of_tvar tvar, ())) fv) Env.empty in *)
    let fml, _, _ = rename_in_formula Env.empty (Core.List.zip_exn fv fv) fml in
    fml
  in
  let mk_bind binder bounds fml =
    if bounds = [] then
      fml
    else
      Formula.mk_bind binder bounds fml Dummy
  in
  let rec move_to_front_in_formula fml =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      Formula.mk_atom (move_to_front_in_atom atom) info, [], []
    else if Formula.is_neg fml then
      let negop, fml, info = Formula.let_unop fml in
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      Formula.mk_unop negop fml info, exists_bounds, forall_bounds
    else if Formula.is_imply fml then
      (* TODO *)
      (Printf.eprintf "not implemented\n";
       assert false)
    else if Formula.is_iff fml then
      (* TODO *)
      (Printf.eprintf "not implemented\n";
       assert false)
    else if Formula.is_and fml || Formula.is_or fml then
      let binop, left_fml, right_fml, info = Formula.let_binop fml in
      let left_fml, left_forall_bounds, left_exists_bounds = move_to_front_in_formula left_fml in
      let right_fml, right_forall_bounds, right_exists_bounds = move_to_front_in_formula right_fml in
      Formula.mk_binop binop left_fml right_fml info, left_forall_bounds @ right_forall_bounds, left_exists_bounds @ right_exists_bounds
    else if Formula.is_bind fml then
      let binder, bounds, fml, _ = Formula.let_bind fml in
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      let binder_bounds, another_bounds =
        match binder with
        | Formula.Forall -> forall_bounds, exists_bounds
        | Formula.Exists -> exists_bounds, forall_bounds
      in
      let fml = mk_bind (Formula.flip_quantifier binder) another_bounds fml in
      let another_bounds = [] in
      let binder_bounds = bounds @ binder_bounds in
      let forall_bounds, exists_bounds =
        match binder with
        | Formula.Forall -> binder_bounds, another_bounds
        | Formula.Exists -> another_bounds, binder_bounds
      in
      fml, forall_bounds, exists_bounds
    else
      assert false
  and move_to_front_in_atom atom =
    if Atom.is_app atom then
      let pred, args, info = Atom.let_app atom in
      Atom.mk_app (move_to_front_in_predicate pred) args info
    else if Atom.is_true atom || Atom.is_false atom then
      atom
    else
      assert false
  and move_to_front_in_predicate pred =
    if Predicate.is_fix pred then
      let fix, pvar, arg_sorts, body = Predicate.let_fix pred in
      Predicate.mk_fix fix pvar arg_sorts (move_to_front body)
    else if Predicate.is_psym pred || Predicate.is_var pred then
      pred
    else
      assert false
  and move_to_front fml =
    let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
    mk_bind Formula.Forall forall_bounds
    @@ mk_bind Formula.Exists exists_bounds fml
  in
  move_to_front @@ rename fml


(* Note: Assuming that there are no binders and fixpoints in the given input.  *)
let into_nnf phi =
  let open Formula in
  let flip = function | And -> Or | Or -> And | _ -> assert false in
  (*  print_endline @@ "phinnf:" ^ (PrinterHum.str_of_formula phi); *)
  let rec inner phi =
    match phi with
    | Atom _ -> phi
    | UnaryOp (Neg, Atom _, _) -> phi
    | UnaryOp (Neg, UnaryOp(Neg, phi, _), _) -> phi
    | UnaryOp (Neg, BinaryOp(op, a, b, info), info') ->
      BinaryOp(flip op, inner (Formula.mk_neg a info),
               inner (Formula.mk_neg b info), info')
    | UnaryOp (Neg, LetRec([], phi, _), info) -> inner (Formula.mk_neg phi info)
    | BinaryOp (op, a, b, info) -> BinaryOp (op, inner a, inner b, info)
    | LetRec([], phi, _) -> inner phi
    | _ -> failwith @@ "can not have binder or fixpoints : " ^ (Printer.str_of_formula phi)
  in inner phi

(* Note: Assuming that there are no binders and fixpoints in the given input *)
let into_cnf_naive phi =
  (*  print_endline @@ "raw:" ^ (PrinterHum.str_of_formula phi);*)
  let open Formula in
  let rec de_morgan phi =
    match phi with
    | Atom _ -> phi
    (* (A /\ B) \/ C -> (A \/ C) /\ (B \/ C) *)
    | BinaryOp (op, LetRec([], phi1, _), phi2, info)
    | BinaryOp (op, phi1, LetRec([], phi2, _), info) ->
      de_morgan (Formula.mk_binop op phi1 phi2 info)
    | BinaryOp (Or, BinaryOp(And, a, b, _), c, _) ->
      let a_or_c = Formula.mk_or a c Dummy in
      let b_or_c = Formula.mk_or b c Dummy in
      Formula.mk_and a_or_c b_or_c Dummy
    (* A \/ (B /\ C) -> (A' \/ B') /\ (A' \/ C') *)
    | BinaryOp (Or, a, BinaryOp(And, b, c, i), i') ->
      de_morgan (BinaryOp (Or, BinaryOp(And, b, c, i), a, i'))
    | BinaryOp (op, a, b, info) ->
      BinaryOp (op, de_morgan a, de_morgan b, info)
    | UnaryOp (Neg, LetRec([], phi, _), info) -> de_morgan (Formula.mk_neg phi info)
    | UnaryOp (_, phi, info) -> Formula.mk_neg (de_morgan phi) info
    | LetRec([], body, _) -> de_morgan body
    | _ -> failwith @@ "can not contain binders or fixpoints : " ^ (Printer.str_of_formula phi)
  in
  let rec inner phi =
    let phi' = de_morgan phi in
    if phi = phi' then phi'
    else inner phi'
  in
  let nnf = into_nnf phi in
  let cnf = inner nnf in
  cnf
(*  print_endline @@ "nnf:" ^ PrinterHum.str_of_formula nnf;
    print_endline @@ "cnf:" ^ PrinterHum.str_of_formula cnf; cnf *)
