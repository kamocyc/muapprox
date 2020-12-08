open Z3
open Util
open Ast.Logic
open Ast

let of_var ctx (Ident.Tvar var) =
  var |> String.escaped |> Symbol.mk_string ctx

let debug_print_z3_input phis =
  let open Fptprover in
  if (!Global.config).debug_print_z3_input then begin
    Debug.print "Z3 input formulas :";
    List.iter (fun phi -> Debug.print @@ Expr.to_string phi) phis;
  end

let debug_print_z3_model model =
  let open Fptprover in
  if (!Global.config).debug_print_z3_model then begin
    Debug.print @@ "Z3 output model :" ^ Model.to_string model;
  end

let int_type ctx = Arithmetic.Integer.mk_sort ctx
let bool_type ctx = Boolean.mk_sort ctx
let real_type ctx = Arithmetic.Real.mk_sort ctx
let list_type s ctx = Z3List.mk_sort ctx (Symbol.mk_string ctx "list") s
let fun_type t1 t2 ctx = Z3Array.mk_sort ctx t1 t2

let tuple_type sorts ctx =
  let num = List.length sorts in
  Tuple.mk_sort ctx
    ("tuple" ^ string_of_int num |> Symbol.mk_string ctx)
    (Core.List.init num
       ~f:(fun i -> "get_" ^ Ordinal.string_of @@ Ordinal.make i |> Symbol.mk_string ctx))
    sorts

let sorts_of_tuple sort =
  sort
  |> Tuple.get_mk_decl
  |> FuncDecl.get_domain

let sort_of s = match Z3.Sort.get_sort_kind s with
  | Z3enums.BOOL_SORT -> T_bool.SBool
  | Z3enums.INT_SORT -> T_int.SInt
  | Z3enums.REAL_SORT -> T_int.SReal
  | _ -> assert false (* TODO: implement others *)


(* from Z3 expr to our term *)
(* term_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.Term.t *)
let rec term_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) expr = try
    let mk_binop op expr =
      match Expr.get_args expr with
      | e :: es ->
        List.fold_left
          (fun acc e -> op acc (term_of senv penv e) Dummy)
          (term_of senv penv e)
          es
      | _ -> assert false
    in
    if Expr.ast_of_expr expr |> AST.is_var then begin
      let var = Expr.to_string expr in
      let index = Env.length senv - Scanf.sscanf var "(:var %d)" (fun x -> x) - 1 in
      let (var, sort) = Env.nth senv index in
      Term.mk_var var sort Dummy
    end
    else if Arithmetic.is_int_numeral expr then
      T_int.mk_int (Bigint.of_string @@ Big_int.string_of_big_int @@ Arithmetic.Integer.get_big_int expr) Dummy
    else if Arithmetic.is_real expr then
      let open Extarithmetic in
      T_int.mk_real (Arithmetic.Real.numeral_to_string expr) Dummy
    else if Arithmetic.is_add expr then
      mk_binop T_int.mk_add expr
    else if Arithmetic.is_sub expr then
      mk_binop T_int.mk_sub expr
    else if Arithmetic.is_mul expr then
      mk_binop T_int.mk_mult expr
    else if Arithmetic.is_div expr || Arithmetic.is_idiv expr then
      mk_binop T_int.mk_div expr
    else if Expr.is_const expr then
      match Expr.to_string expr with
      | "true" -> T_bool.mk_bool (Atom.mk_true Dummy) Dummy
      | "false" -> T_bool.mk_bool (Atom.mk_false Dummy) Dummy
      | str ->
        try
          T_int.mk_int (Bigint.of_string str) Dummy
        with Failure _ -> begin
            let sort = Env.lookup (Ident.Tvar str) senv in
            Term.mk_var (Ident.Tvar str) sort Dummy
          end
    else
      T_bool.mk_bool (atom_of senv penv expr) Dummy
  with _ ->
    Printf.printf "fail when parsing z3 expr %s into our format" @@ Expr.to_string expr;
    assert false
and
  (* from Z3 expr to our atom *)
  (* atom_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.Atom.t *)
  atom_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) expr =
  let mk_binop op =
    match Expr.get_args expr with
    | [expr1; expr2] ->
      let t1 = term_of senv penv expr1 in
      let t2 = term_of senv penv expr2 in
      op t1 t2 Dummy
    | _ -> assert false
  in
  if Boolean.is_true expr then Atom.mk_true Dummy
  else if Boolean.is_false expr then Atom.mk_false Dummy
  else if Boolean.is_eq expr then
    mk_binop T_bool.mk_eq
  else if Arithmetic.is_le expr then
    mk_binop T_int.mk_leq
  else if Arithmetic.is_ge expr then
    mk_binop T_int.mk_geq
  else if Arithmetic.is_lt expr then
    mk_binop T_int.mk_lt
  else if Arithmetic.is_gt expr then
    mk_binop T_int.mk_gt
  else
    assert false (* TODO: implement others *)
and
  (* from Z3 expr to our formula *)
  (* formula_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.Formula.t *)
  formula_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) expr =
  if Boolean.is_not expr then
    match Expr.get_args expr with
    | [body] -> Formula.mk_neg (formula_of senv penv body) Dummy
    | _ -> assert false
  else if Boolean.is_and expr then
    (Expr.get_args expr |> List.map (formula_of senv penv) |> Formula.and_of) Dummy
  else if Boolean.is_or expr then
    (Expr.get_args expr |> List.map (formula_of senv penv) |> Formula.or_of) Dummy
  else if Boolean.is_iff expr then
    Expr.get_args expr |> List.map (formula_of senv penv) |> function
    | [phi1; phi2] -> Formula.mk_iff phi1 phi2 Dummy
    | _ -> assert false
  else if Boolean.is_implies expr then
    Expr.get_args expr |> List.map (formula_of senv penv) |> function
    | [phi1; phi2] -> Formula.mk_imply phi1 phi2 Dummy
    | _ -> assert false
  else if Expr.ast_of_expr expr |> AST.is_quantifier then begin
    let q = Quantifier.quantifier_of_expr expr in
    let binder =
      if Quantifier.is_universal q then Formula.Forall
      else Formula.Exists in
    let bounds = (* Option.unwrap @@ *) Core.List.zip_exn (* The type of core.List.zip is changed in the latest core library *)
        (Quantifier.get_bound_variable_names q |> List.map (fun x -> Ident.Tvar (Symbol.get_string x)))
        (Quantifier.get_bound_variable_sorts q |> List.map sort_of) in
    let senv = Env.update bounds senv in
    let body = Quantifier.get_body q |> formula_of senv penv in
    Formula.mk_bind binder bounds body Dummy
  end
  else Formula.mk_atom (atom_of senv penv expr) Dummy

(* from our sort to Z3 sort *)
let of_sort ctx = function
  | T_int.SInt -> int_type ctx
  | T_int.SReal -> real_type ctx
  | T_bool.SBool -> bool_type ctx
  | _ -> assert false

(* from our predicate to Z3 funcdecl *)
let of_predicate _ (_: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) pred =
  if Predicate.is_var pred then
    let pvar, _ = Predicate.let_var pred in
    Env.lookup pvar penv
  else assert false

(* from our formula to Z3 expr *)
(* of_formula: Z3.context -> (Ident.tvar, Sort.t) Env.t -> info Logic.Formula.t *)
let rec of_formula ctx (env: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) phi =
  let mk_binop_expr dtor ctor =
    let phi1, phi2, _ = dtor phi in
    [of_formula ctx env penv phi1; of_formula ctx env penv phi2] |> ctor ctx
  in
  if Formula.is_atom phi then
    let atom, _ = Formula.let_atom phi in
    of_atom ctx env penv atom
  else if Formula.is_neg phi then
    Boolean.mk_not ctx @@ of_formula ctx env penv @@ fst (Formula.let_neg phi)
  else if Formula.is_and phi then
    mk_binop_expr Formula.let_and Boolean.mk_and
  else if Formula.is_or phi then mk_binop_expr Formula.let_or Boolean.mk_or
  else if Formula.is_imply phi then
    let phi1, phi2, _ = Formula.let_imply phi in
    Boolean.mk_implies ctx
      (of_formula ctx env penv phi1)
      (of_formula ctx env penv phi2)
  else if Formula.is_bind phi then
    let binder, bounds, body, _ = Formula.let_bind phi in
    let builder =
      if binder = Formula.Forall then Quantifier.mk_forall
      else if binder = Formula.Exists then Quantifier.mk_exists
      else assert false
    in
    let bounds = List.rev bounds in
    let env = Env.update bounds env in
    let sorts = Env.elems bounds |> List.map (of_sort ctx) in
    let vars = Env.keys bounds |> List.map (of_var ctx) in
    let body = of_formula ctx env penv body in
    builder
      ctx sorts vars body
      None [] [] None None
    |> Quantifier.expr_of_quantifier
  else if Formula.is_letrec phi then
    match Formula.let_letrec phi with
    | [], phi, _ -> of_formula ctx env penv phi
    | _, _, _ ->
      failwith @@  "underlying solver can not deal with fixpoint predicate : " ^ Convert.PrinterHum.str_of_formula phi;
  else assert false

(* from our term to Z3 expr *)
and of_term ctx (env: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) t =
  if Term.is_var t then
    let var, sort, _ = Term.let_var t in
    match Env.lookupi_ var env with
    | Some(sort', i) ->
      assert (sort = sort');
      let sort = of_sort ctx sort in
      Quantifier.mk_bound ctx i sort
    | None ->
      let symbol = of_var ctx var in
      let sort = of_sort ctx sort in
      Expr.mk_const ctx symbol sort
  else if Term.is_funapp t then
    match Term.let_funapp t with
    | T_bool.Bool atom, [], _ -> of_atom ctx env penv atom
    | T_bool.Formula phi, [], _ -> of_formula ctx env penv phi
    | T_bool.IfThenElse, [cond; then_; else_], _ ->
      let cond = of_term ctx env penv cond in
      let then_ = of_term ctx env penv then_ in
      let else_ = of_term ctx env penv else_ in
      Boolean.mk_ite ctx cond then_ else_
    | T_int.Int n, [], _ -> Arithmetic.Integer.mk_numeral_s ctx (Bigint.to_string n)
    | T_int.Real f, [], _ -> Arithmetic.Real.mk_numeral_s ctx f
    | T_int.Add, [t1; t2], _ ->
      [of_term ctx env penv t1; of_term ctx env penv t2]
      |> Arithmetic.mk_add ctx
    | T_int.Sub, [t1; t2], _ ->
      [of_term ctx env penv t1; of_term ctx env penv t2]
      |> Arithmetic.mk_sub ctx
    | T_int.Mult, [t1; t2], _ ->
      [of_term ctx env penv t1; of_term ctx env penv t2]
      |> Arithmetic.mk_mul ctx
    | T_int.Div, [t1; t2], _ ->
      Arithmetic.mk_div ctx
        (of_term ctx env penv t1)
        (of_term ctx env penv t2)
    | T_int.Mod, [t1; t2], _ ->
      Arithmetic.Integer.mk_mod ctx
        (of_term ctx env penv t1)
        (of_term ctx env penv t2)
    | T_int.UnaryNeg, [t], _ ->
      Arithmetic.mk_unary_minus ctx (of_term ctx env penv t)
    | _ -> assert false
  else assert false
and
  (* from our atom to Z3 expr *)
  of_atom ctx (env: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) atom =
  if Atom.is_true atom then
    Boolean.mk_true ctx
  else if Atom.is_false atom then
    Boolean.mk_false ctx
  else if Atom.is_symapp atom then
    let sym, args, _ = Atom.let_symapp atom in
    let builder = match sym with
      | T_bool.Eq -> Boolean.mk_eq
      | T_int.Leq -> Arithmetic.mk_le
      | T_int.Geq -> Arithmetic.mk_ge
      | T_int.Lt -> Arithmetic.mk_lt
      | T_int.Gt -> Arithmetic.mk_gt
      | T_bool.Neq ->
        (fun ctx left_fml right_fml ->
           Boolean.mk_not ctx @@ Boolean.mk_eq ctx left_fml right_fml
        )
      | _ -> assert false (* TODO: implement *)
    in
    match args with
    | [t1; t2] ->
      builder ctx (of_term ctx env penv t1) (of_term ctx env penv t2)
    | _ -> assert false
  else if Atom.is_app atom then
    let (pred, args, _) = Atom.let_app atom in
    Expr.mk_app ctx (of_predicate ctx env penv pred) (List.map (fun arg -> of_term ctx env penv arg) args)
  else assert false

let map_of_model model =
  let open Core in
  let decls = Model.get_decls model in
  List.map decls ~f:(fun decl ->
      let ident = Symbol.get_string (FuncDecl.get_name decl) in
      match Model.get_const_interp model decl with
      | Some(expr) ->
        let t = term_of Env.empty Env.empty expr in
        Ident.Tvar ident, Some t
      | None -> Ident.Tvar ident, None)

let check_sat_z3 phis context =
  let solver = Solver.mk_solver context None in
  Solver.add solver phis;
  debug_print_z3_input phis;
  match Solver.check solver [] with
  | SATISFIABLE -> Solver.get_model solver >>= fun model ->
    debug_print_z3_model model;
    (*if (!Fptprover.Global.config).smart_model then
      Some (smart_map_of_model model phis context)
      else*)
    Some (map_of_model model)
  | _ -> None

let check_sat phis =
  let cfg = [
    ("MODEL", "true");
    (* ("well_sorted_check", "true"); *)
  ] in
  let ctx = mk_context cfg in
  let phis = List.map (fun phi -> of_formula ctx Env.empty Env.empty phi) phis in
  check_sat_z3 phis ctx

let check_satisfiability = check_sat

let check_validity phi =
  let phi = Formula.mk_neg phi Dummy in
  check_sat [phi]

let solve phis = Core.Option.is_some (check_sat phis)

let check_validity_with_range range phi =
  let phi = Formula.mk_neg phi Dummy in
  let phi = Formula.mk_and phi range Dummy in
  check_sat [phi]

let map_of_model model =
  let open Core in
  let decls = Model.get_const_decls model in
  List.map decls ~f:(fun decl ->
      (Ident.Tvar (Symbol.get_string (FuncDecl.get_name decl)),
       Model.get_const_interp model decl >>= fun expr ->
       Some(term_of Env.empty Env.empty expr)))

module SAT :sig
  val check_sat: Proplogic.Formula.t -> (Proplogic.Formula.t * Proplogic.Formula.t option) list option
  val solve_and_seek: int -> Proplogic.Formula.t -> (string * bool) list list
end = struct
  open Proplogic.Formula

  let rec of_formula ctx = function
    | True _ -> Z3.Boolean.mk_true ctx
    | False _ -> Z3.Boolean.mk_false ctx
    | Atom (id, _) ->
      let symbol = id |> String.escaped |> Symbol.mk_string ctx in
      Expr.mk_const ctx symbol (bool_type ctx)
    (*Z3.Boolean.mk_const_s ctx id*)
    | UnaryOp (Neg, t, _) -> Z3.Boolean.mk_not ctx (of_formula ctx t)
    | BinaryOp (And, t1, t2, _) ->
      Z3.Boolean.mk_and ctx [of_formula ctx t1; of_formula ctx t2]
    | BinaryOp (Or, t1, t2, _) ->
      Z3.Boolean.mk_or ctx [of_formula ctx t1; of_formula ctx t2]

  let formula_of expr =
    if Expr.is_const expr then
      match Expr.to_string expr with
      | "true" -> mk_true Dummy
      | "false" -> mk_false Dummy
      | _ -> assert false
    else assert false

  let map_of_model model =
    let open Core in
    let decls = Model.get_const_decls model in
    (* print_endline @@ "num_of_decls" ^ (string_of_int (List.length decls));*)
    List.map decls ~f:(fun decl ->
        (mk_atom (Symbol.get_string (FuncDecl.get_name decl)) Dummy,
         Model.get_const_interp model decl >>= fun expr ->
         Some(formula_of expr)))

  (* Propositional Logic Satisfiability *)
  let check_sat phi =
    (*Z3.set_global_param "sat.core.minimize" "true";
      Z3.set_global_param "smt.core.minimize" "true";*)
    let cfg = [
      ("MODEL", "true");
      ("well_sorted_check", "true");
      (*        ("sat.core.minimize", "true");
                ("smt.core.minimize", "true") *)
      (*        ("MBQI", "false"); *)
    ] in
    let ctx = mk_context cfg in
    let solver = Solver.mk_solver ctx None in
    let phi = of_formula ctx phi in
    (* print_endline @@ "cheking phi:" ^ (Z3.Expr.to_string phi); *)
    Solver.add solver [phi];
    debug_print_z3_input [phi];
    match Solver.check solver [] with
    | SATISFIABLE ->
      Solver.get_model solver >>= fun model ->
      debug_print_z3_model model;
      Some (map_of_model model)
      (*
      if (!Fptprover.Global.config).smart_model then
        Some (smart_map_of_model model [phi] ctx)
      else
        Some (map_of_model model)
       *)
    | _ -> None

  let rec solve_and_seek maximum formula =
    if maximum < 0 then
      failwith "maximum cannot be negative"
    else if maximum = 0 then
      []
    else
      match check_sat formula with
      | None -> []
      | Some model ->
        let solution = List.map (function
            | (Proplogic.Formula.Atom (name, _), Some (Proplogic.Formula.True _)) -> (name, true)
            | (Proplogic.Formula.Atom (name, _), Some (Proplogic.Formula.False _)) -> (name, false)
            | _ -> failwith "invalid model") model in
        let negation = Proplogic.Formula.or_of
            (List.map (fun (variable, boolean) ->
                 if boolean then Proplogic.Formula.mk_neg (Proplogic.Formula.mk_atom variable Dummy) Dummy
                 else Proplogic.Formula.mk_atom variable Dummy) solution) Dummy in
        let formula' = Proplogic.Formula.mk_and formula negation Dummy in
        solution :: solve_and_seek (maximum - 1) formula'
end
