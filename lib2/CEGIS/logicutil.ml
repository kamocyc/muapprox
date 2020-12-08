open Core open Core.Poly
open Ast.Logic
open Ast

type position = Pos | Neg

let negpos = function
  | Pos -> Neg
  | Neg -> Pos

type rule = Predicate.fixpoint * position

(* TODO: to be tail recursion *)
let rec sorts_of_params = function
  | [] -> []
  | (_, sort) :: xs -> sort :: (sorts_of_params xs)

(*
  negpos -> Formula.t -> (rule * Predicate.t * Formula.t) Option
  outputs:
   rule: which rule that we apply
   Predicate.t: found fixpoint predicate
   Formula.t: context
*)
let rec find_fixpoint position phi = let open Formula in
  match phi with
  | Atom (atom, info) ->
    find_fixpoint_atom position atom
    |> Option.map ~f:(fun (rule, pred, atom) -> rule, pred, mk_atom atom info)
  | UnaryOp (Neg, phi, info) ->
    find_fixpoint (negpos position) phi
    |> Option.map ~f:(fun (rule, pred, phi) -> rule, pred, mk_neg phi info)
  | BinaryOp (op, phi1, phi2, info) when op = And || op = Or ->
    Util.Option.compose
      (find_fixpoint position phi1
       |> Option.map ~f:(fun (rule, pred, phi1) -> rule, pred, mk_binop op phi1 phi2 info))
      (find_fixpoint position phi2
       |> Option.map ~f:(fun (rule, pred, phi2) -> rule, pred, mk_binop op phi1 phi2 info))
  | LetRec (bounded, phi, _) -> begin
      match find_fixpoint position phi, bounded with
      | Some (x), _ -> Some (x)
      | None, (fp, pvar, params, phi') :: xs -> begin
          let args = List.map ~f:(fun (_, sort) ->
              Term.mk_var (Ident.mk_fresh_tvar ()) sort Dummy
            ) params in
          let app = mk_atom
              (Atom.mk_app
                 (Predicate.Fixpoint (fp, pvar, params, phi'))
                 args
                 Dummy)
              Dummy in
          let rest = mk_letrec xs phi Dummy in
          let phi = mk_and app rest Dummy in
          find_fixpoint position phi
        end
      | None, [] -> None
    end
  | _ -> failwith "invalid formula"

and find_fixpoint_atom position atom = let open Atom in
  match atom with
  | True _ | False _ -> None
  | App (pred, args, info) ->
    Util.Option.compose
      (find_fixpoint_pred position pred
       |> Option.map ~f:(fun (rule, pred, p) -> rule, pred, App(p, args, info)))
      (List.find_map ~f:(fun arg -> find_fixpoint_term position arg) args)

(*
  negpos -> Predicate.t -> (rule * Predicate.t * Predicate.t) Option
  outputs:
   rule: which rule that we apply
   Predicate.t: found inner fixpoint predicate
   Predicate.t: context
*)
and find_fixpoint_pred position pred = let open Predicate in
  match pred with
  | Var _ | Psym _ -> None
  | Fixpoint (fp, ident, params, phi) -> begin
      match find_fixpoint position phi with
      | Some (rule, inner_pred, context) -> Some (rule, inner_pred, Fixpoint(fp, ident, params, context))
      | None ->
        let rule = fp, position in
        let sorts = sorts_of_params params in
        Some(rule, Fixpoint (fp, ident, params, phi), Var (ident, sorts))
    end

and find_fixpoint_term _position term = let open Term in
  match term with
  | Var _ -> None
  | FunApp (_sym, _args, _) -> None (* TODO *)

let find_fixpoint = find_fixpoint Pos

(* (Ident.Tvar * Sort.t) list -> Term.t list *)
let args_of_params params =
  let open Term in
  let rec aux acc = function
    | [] -> acc
    | (ident, sort) :: xs ->
      let arg = Var (ident, sort, Dummy) in
      aux (arg :: acc) xs in
  aux [] @@ List.rev params

let sorts_of_params params =
  let rec aux acc = function
    | [] -> acc
    | (_, sort) :: xs ->
      aux (sort :: acc) xs
  in
  aux [] params


let rec all_fixpoints_of_formula pos = function
  | Formula.Atom (atom, _) -> all_fixpoints_of_atom pos atom
  | Formula.UnaryOp (Formula.Neg, phi, _) ->
    all_fixpoints_of_formula (negpos pos) phi
  | Formula.BinaryOp ((Formula.And | Formula.Or), phi1, phi2, _) ->
    (all_fixpoints_of_formula pos phi1) @ (all_fixpoints_of_formula pos phi2)
  | Formula.BinaryOp (Formula.Imply, phi1, phi2, _) ->
    (all_fixpoints_of_formula (negpos pos) phi1)
    @ (all_fixpoints_of_formula pos phi2)
  | Formula.Bind (_, _, phi, _) -> all_fixpoints_of_formula pos phi
  | Formula.LetRec (bounded, phi, _) ->
    (List.map ~f:(fun (fp, _, _, _) -> (fp, Pos)) bounded) @
    (List.map ~f:(fun (fp, _, _, _) -> (fp, Neg)) bounded) @
    (all_fixpoints_of_formula pos phi)
  | phi -> failwith (Convert.PrinterHum.str_of_formula phi)
and
  all_fixpoints_of_atom pos =
  let open Atom in
  function
  | True _ | False _ -> []
  | App (Fixpoint (fp, _, _, phi), _, _) ->
    (fp, pos)::(all_fixpoints_of_formula pos phi)
  | _ -> []

let all_fixpoints_of_formula = all_fixpoints_of_formula Pos

open Ast
open Gather

let paramvar_filter (Ast.Ident.Tvar ident) =
  (String.substr_index ~pattern:"paramvar" ident) <> None

let paramvars_in phi =
  let terms, _ = List.unzip @@
    Variables.to_list @@
    free_variables_of_formula phi in
  terms |> List.filter ~f:paramvar_filter

let not_paramvars_in phi =
  free_variables_of_formula phi
  |> Variables.to_list
  |> List.unzip
  |> (fun (terms, _) ->
      List.filter ~f:(fun x -> not (paramvar_filter x)) terms)

let remove_dontcare phi =
  let open Ast.Logic in
  let paramvars = paramvars_in phi in
  let map = List.map ~f:(fun tvar -> (tvar, T_int.zero Dummy)) paramvars
            |> Map.Poly.of_alist_exn in
  Formula.subst map phi

let remove_dontcare_terms phi =
  let termvars = not_paramvars_in phi in
  let map = List.map ~f:(fun tvar -> (tvar, T_int.zero Dummy)) termvars
            |> Map.Poly.of_alist_exn in
  Formula.subst map phi

let div_params params f =
  let rec aux (acc1, acc2) = function
    | [] -> (List.rev acc1), (List.rev acc2)
    | x :: xs when f x -> aux (x :: acc1, acc2) xs
    | x :: xs -> aux (acc1, x :: acc2) xs
  in
  aux ([], []) params

type termlit = IntLit of Bigint.t | RealLit of float | BoolLit of bool

let term_of_termlit =function
  | IntLit i    -> T_int.mk_int i Dummy
  | RealLit r   -> T_int.mk_real (string_of_float r) Dummy
  | BoolLit b   -> T_bool.mk_bool (if b then Atom.True Dummy else Atom.False Dummy) Dummy

let uneg_of_termlit = function
  | IntLit i -> IntLit (Bigint.neg i) | RealLit r -> RealLit (-.r)
  | BoolLit _ -> failwith "Boolean cannot be negated."

(*
let app_op_to_termlit opi opbi opr opb t1 t2 =
  ignore(opi);
  match t1, t2 with
  | BigIntLit bi1, BigIntLit bi2 ->
     Printf.printf "BigIntLit(%s), BigIntLit(%s)" (Big_int.string_of_big_int bi1) (Big_int.string_of_big_int bi2);
     let bi' = opbi bi1 bi2 in
     begin
       match Big_int.int_of_big_int_opt bi' with
       | None ->  BigIntLit bi'
       | Some i -> IntLit i
     end
  | RealLit r1, RealLit r2 -> print_endline "R + R"; RealLit (opr r1 r2)
  | BoolLit b1, BoolLit b2 -> print_endline "B + B"; BoolLit (opb b1 b2)
  | _ -> failwith "type error"
*)

let app_op opi opr opb t1 t2 =
  match t1, t2 with
  | IntLit i1, IntLit i2   -> IntLit (opi i1 i2)
  | RealLit r1, RealLit r2 -> RealLit (opr r1 r2)
  | BoolLit b1, BoolLit b2 -> BoolLit (opb b1 b2)
  | _ -> failwith "type error @ app_op"

let app_binop =
  let open Formula in function
    | And -> (&&) | Or -> (||) | Imply -> (fun phi1 phi2 -> (not phi1) || phi2) | Iff -> (=)

let str_of_numlit = function
  | IntLit i -> Printf.sprintf "IntLit(%s)" (Bigint.to_string_hum i)
  | BoolLit true -> "true" | BoolLit false -> "false" | RealLit f -> string_of_float f

let compare_numlit opi opr opb t1 t2 =
  match t1, t2 with
  | IntLit  i1, IntLit  i2 -> opi i1 i2
  | RealLit r1, RealLit r2 -> opr r1 r2
  | BoolLit b1, BoolLit b2 -> opb b1 b2
  | _ -> failwith "type error@compare_numlit"

let app_pred pred_sym =
  let dummy = fun _ _ -> failwith "type error@app_pred" in
  match pred_sym with
  | T_int.Leq  -> compare_numlit (Bigint.(<=)) (<=) dummy
  | T_int.Geq  -> compare_numlit (Bigint.(>=)) (>=) dummy
  | T_int.Lt   -> compare_numlit (Bigint.(<)) (<) dummy
  | T_int.Gt   -> compare_numlit (Bigint.(>)) (>) dummy
  | T_bool.Eq  -> compare_numlit (Bigint.(=)) (=) (=)
  | T_bool.Neq -> compare_numlit (Bigint.(<>)) (<>) (<>)
  | _ -> failwith "invalid comparation@app_pred."

let negate_atom =
  let open Formula in function
    | Atom.True info -> Atom(Atom.False info, Dummy)
    | Atom.False info -> Atom(Atom.True info, Dummy)
    | Atom.App (_, _, info) as atom -> UnaryOp(Neg, Atom (atom, info), Dummy)

let rec eval_formula : Formula.t -> bool =
  let open Formula in function
    | Atom (atom, _) -> eval_atom atom
    | UnaryOp (Neg, phi, _) -> not (eval_formula phi)
    | BinaryOp (op, phi1, phi2, _) -> app_binop op (eval_formula phi1) (eval_formula phi2)
    | LetRec(_, _, _) | Bind(_, _, _, _) -> failwith "LetRec and Bind cannot be evaluated into bool value."
and eval_atom : Atom.t -> bool = function
  | Atom.True _ -> true | Atom.False _ -> false
  | Atom.App (Predicate.Psym pred_sym, terms, _) -> eval_pred pred_sym true terms
  | Atom.App ((Predicate.Var(_, _) | Predicate.Fixpoint(_, _, _, _)), _, _) ->
    failwith "Predicate variables and fixpoints cannot be evaluated into bool value."
and eval_pred pred_sym acc = function
  | [] -> acc
  | _::[] -> failwith "This case cannot happen."
  | t1::t2::[] -> acc && app_pred pred_sym (eval_term t1) (eval_term t2)
  | t1::t2::ts -> eval_pred pred_sym (acc && app_pred pred_sym (eval_term t1) (eval_term t2)) (t2::ts)
and eval_term = function
  | Term.Var _ -> failwith "Any term variables should be removed before evaluating formula."
  | Term.FunApp (T_int.Int i, _, _) -> IntLit i
  | Term.FunApp (T_int.Real r, _, _) -> RealLit (float_of_string r)
  | Term.FunApp (T_bool.Bool (Atom.True _), _, _) -> BoolLit true
  | Term.FunApp (T_bool.Bool (Atom.False _), _, _) -> BoolLit false
  | Term.FunApp (T_bool.Bool _, _, _) -> failwith "This case cannot happen."
  | Term.FunApp ((T_int.Add | T_int.Sub | T_int.Mult | T_int.Div | T_int.Mod) as fun_sym, terms, _) ->
    eval_terms fun_sym terms
  | Term.FunApp (T_int.UnaryNeg, [term], _) -> eval_term term |> uneg_of_termlit
  | Term.FunApp (T_bool.Formula phi, _, _) -> BoolLit (eval_formula phi)
  | Term.FunApp (T_bool.IfThenElse, [cond_; then_; else_], _) ->
    begin
      match eval_term cond_ with
      | BoolLit true -> eval_term then_
      | BoolLit false -> eval_term else_
      | _ -> failwith "type error"
    end
  | _ -> failwith "Unimplemented in eval term"
and eval_terms fun_sym = function
  | [] -> failwith "0 ary functions are forbidden here."
  | t::[] -> eval_term t
  | t::ts -> app_fun fun_sym (eval_term t) (eval_terms fun_sym ts)
and app_fun fun_sym t1 t2 =
  let dummy = fun _ _ -> assert false in
  match fun_sym with
  | T_int.Add  -> app_op (Bigint.(+))   (+.)  dummy t1 t2
  | T_int.Sub  -> app_op (Bigint.(-))   (-.)  dummy t1 t2
  | T_int.Mult -> app_op (Bigint.( * )) ( *.) dummy t1 t2
  | T_int.Div  -> app_op (Bigint.(/))   (/.)  dummy t1 t2
  | T_int.Mod  -> app_op (Bigint.(%)) (Float.mod_float) dummy t1 t2
  | _ -> failwith "this state cannot happen."


let rec eval_nnf_formula_with_papps : Formula.t -> Formula.t =
  let open Formula in function
    | Atom (atom, _) -> Atom (eval_atom_with_papps atom, Dummy)
    | UnaryOp (Neg, Atom(atom, _), _) -> eval_atom_with_papps atom |> negate_atom
    | BinaryOp (And, phi1, phi2, _) ->
      begin
        match eval_nnf_formula_with_papps phi1, eval_nnf_formula_with_papps phi2 with
        | Atom(False _, _), _ | _, Atom(Atom.False _, _) -> Atom(False Dummy, Dummy)
        | Atom(True _, _), phi | phi, Atom(Atom.True _, _) -> phi
        | phi1, phi2 -> BinaryOp(And, phi1, phi2, Dummy)
      end
    | BinaryOp (Or, phi1, phi2, _) ->
      begin
        match eval_nnf_formula_with_papps phi1, eval_nnf_formula_with_papps phi2 with
        | Atom(True _, _), _ | _, Atom(True _, _) -> Atom(True Dummy, Dummy)
        | Atom(False _, _), phi | phi, Atom(False _, _) -> phi
        | phi1, phi2 -> BinaryOp(Or, phi1, phi2, Dummy)
      end
    | UnaryOp (Neg, _, _) -> failwith "Input must be of nnf (Invalid formula appeared inside Neg.)"
    | LetRec(_, _, _) | Bind(_, _, _, _) ->
      failwith "Input must be of nnf (LetRec and Bind appeared.)"
    | BinaryOp (_, _, _, _) as phi ->
      failwith @@ Printf.sprintf
        "Input must be of nnf (Invalid binary operators appeared.) in: %s \n"
        (Convert.PrinterHum.str_of_formula phi)

and eval_atom_with_papps atom =
  match atom with
  | Atom.True _ | Atom.False _ -> atom
  | Atom.App ((Predicate.Var (_, _) | Predicate.Fixpoint(_, _, _, _)), _, _) -> atom
  | Atom.App (Predicate.Psym pred_sym, terms, _) ->
    (*     Printf.printf "@eval_atom_with_papps: %s" @@ Convert.PrinterHum.str_of_atom 20 atom; *)
    match eval_pred pred_sym true terms with
    | true -> Atom.True Dummy
    | false -> Atom.False Dummy

let rec normalize_formula phi =
  let open Atom in
  let open Formula in
  let open T_int in
  match phi with
  | UnaryOp (Neg, phi, _) -> anti_normalize_formula phi
  | Atom (App (Psym Lt, [t1; t2], _), info) -> (* t1 < t2 -> -t1 > -t2 -> -t1 >= -t2+1 *)
    mk_atom (mk_geq (mk_neg t1 info) (mk_add (mk_neg t2 info) (one info) info) info) info
  | Atom (App (Psym Gt, [t1; t2], _), info)-> (* t1 > t2 -> t1 >= t2+1 *)
    mk_atom (mk_geq t1 (mk_add t2 (one info) info) info) info
  | Atom (App (Psym Leq, [t1; t2], _), info) -> (* t1 <= t2 -> -t1 >= -t2 *)
    mk_atom (mk_geq (mk_neg t1 info) (mk_neg t2 info) info) info
  | _ -> phi
and anti_normalize_formula (phi : Logic.Formula.t) : Logic.Formula.t =
  let open Atom in
  let open Formula in
  let open T_int in
  match phi with
  | UnaryOp (Neg, phi, _) -> normalize_formula phi
  | Atom (App (Psym Geq, [t1; t2], _), info) -> (* t1 >= t2 -> -t1 >= -t2+1 *)
    mk_atom (mk_geq (mk_neg t1 info) (mk_add (mk_neg t2 info) (one info) info) info) info
  | Atom (App (Psym Gt, [t1; t2], _), info)-> (* t1 > t2 -> -t1 >= -t2+1 *)
    mk_atom (mk_geq (mk_neg t1 info) (mk_neg t2 info) info) info
  | Atom (App (Psym Leq, [t1; t2], _), info) -> (* t1 <= t2 -> t1 >= t2+1 *)
    mk_atom (mk_geq t1 (mk_add t2 (one info) info) info) info
  | Atom (App (Psym Lt, [t1; t2], _), info) -> (* t1 < t2 -> t1 >= t2 *)
    mk_atom (mk_geq t1 t2 info) info
  | _ -> phi

(* position -> Formula.t ->  *)
let rec find_outest_fixpoint position (ctx: 'a -> Formula.t) phi =
  let open Formula in
  match phi with
  | Atom (atom, info) ->
    let ctx' = fun x -> ctx (mk_atom x info) in
    aux_atom position ctx' atom
  | UnaryOp (Neg, phi, info) ->
    let ctx' = fun x -> ctx (mk_neg x info) in
    find_outest_fixpoint (negpos position) ctx' phi
  | BinaryOp (op, phi1, phi2, info) when op = And || op = Or ->
    let ctx'  = fun x -> ctx (BinaryOp (op, x, phi2, info)) in
    let ctx'' = fun x -> ctx (BinaryOp (op, phi1, x, info)) in
    begin
      match find_outest_fixpoint position ctx' phi1 with
      | Some x -> Some x
      | None -> find_outest_fixpoint position ctx'' phi2
    end
  | LetRec ([], body, info) ->
    let ctx = fun x -> ctx (LetRec ([], x, info)) in
    find_outest_fixpoint position ctx body
  | LetRec ((fp, pvar, params, fp_body) :: tl, body, info) ->
    let ctx = fun x ->
      let pvar', _ = Predicate.let_var x in
      let phi = LetRec (tl, body, info) in
      let phi = Formula.replace_pred_ident pvar pvar' phi in
      ctx phi
    in
    let pred = Predicate.mk_fix fp pvar params fp_body in
    let rule = fp, position in
    Some(rule, pred, ctx)
  | _ -> failwith "invalid formula"

and aux_atom position ctx atom =
  let open Atom in
  match atom with
  | True _ | False _ -> None
  | App (pred, args, info) ->
    let ctx' = fun x -> ctx (mk_app x args info) in
    aux_pred position ctx' pred

and aux_pred position ctx pred =
  let open Predicate in
  match pred with
  | Var _ | Psym _ -> None
  | Fixpoint (fp, _, _, _) ->
    let rule = fp, position in Some(rule, pred, ctx)

let find_outest_fixpoint = find_outest_fixpoint Pos (fun x -> x)


let negation_of (sym, terms, info) =
  assert (List.length terms = 2);
  let t1, t2 = List.nth_exn terms 0, List.nth_exn terms 1 in
  match sym with
  | T_int.Leq -> T_int.mk_gt t1 t2 info
  | T_int.Geq -> T_int.mk_lt t1 t2 info
  | T_int.Lt  -> T_int.mk_geq t1 t2 info
  | T_int.Gt  -> T_int.mk_leq t1 t2 info
  | T_bool.Eq  -> T_bool.mk_neq t1 t2 info
  | T_bool.Neq -> T_bool.mk_eq t1 t2 info
  | _ -> assert false

(* Assuming that phi is of nnf. *)
let rec negated_int_term_simplify phi =
  let open Formula in
  let negation_of (sym, terms, info) =
    assert (List.length terms = 2);
    let t1, t2 = List.nth_exn terms 0, List.nth_exn terms 1 in
    match sym with
    | T_int.Leq -> T_int.mk_gt t1 t2 info
    | T_int.Geq -> T_int.mk_lt t1 t2 info
    | T_int.Lt  -> T_int.mk_geq t1 t2 info
    | T_int.Gt  -> T_int.mk_leq t1 t2 info
    | T_bool.Eq  -> T_bool.mk_neq t1 t2 info
    | T_bool.Neq -> T_bool.mk_eq t1 t2 info
    | _ -> assert false
  in match phi with
  | UnaryOp(Neg, Atom(atom ,_), _) when Atom.is_symapp atom ->
    mk_atom (negation_of (Atom.let_symapp atom)) Dummy
  | UnaryOp(_, _, _) | Atom (_, _) -> phi
  | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, negated_int_term_simplify phi1,
                                               negated_int_term_simplify phi2, info)
  | LetRec(bounded, body, info) -> LetRec(bounded, negated_int_term_simplify body, info)
  | Bind(q, bounded, phi, info)  -> Bind(q, bounded, negated_int_term_simplify phi, info)

(* Assuming that phi is of nnf. *)
let simplify phi =
  let open Logic.Formula in
  let open Logic.Atom in
  let rec inner phi =
    match phi with
    | BinaryOp(Or, Atom(atom, info), phi, info') | BinaryOp(Or, phi, Atom(atom, info), info') ->
      if is_true atom then Atom(atom, info)
      else if is_false atom then phi
      else BinaryOp(Or, Atom(atom, info), inner phi, info')
    | BinaryOp(And, Atom(atom, info), phi, info') | BinaryOp(And, phi, Atom(atom, info), info') ->
      if is_true atom then phi
      else if is_false atom then Atom(atom, info)
      else BinaryOp(And, Atom(atom, info), inner phi, info')
    | Atom (_, _) -> phi
    | UnaryOp(Neg, phi1, info) -> UnaryOp(Neg, inner phi1, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, inner phi1, inner phi2, info)
    | _ -> failwith "simplify assumes that the given input is of nnf."
  in
  let phi' = inner phi in if phi = phi' then phi' else inner phi'

let rec nnf_of phi =
  let open Logic in
  let open Logic.Formula in
  match phi with
  | Atom(_, _) -> phi
  | UnaryOp(Neg, Atom(Atom.True info, info'), _)  -> Atom(Atom.False info, info')
  | UnaryOp(Neg, Atom(Atom.False info, info'), _) -> Atom(Atom.True info, info')
  | UnaryOp(Neg, atom, info) when is_atom atom -> UnaryOp(Neg, atom, info)
  | UnaryOp(Neg, UnaryOp(Neg, atom, _), _) -> nnf_of atom
  | UnaryOp(Neg, BinaryOp(And, phi1, phi2, info'), info) ->
    BinaryOp(Or,
             nnf_of (UnaryOp(Neg, phi1, info)),
             nnf_of (UnaryOp(Neg, phi2, info)), info')
  | UnaryOp(Neg, BinaryOp(Or, phi1, phi2, info'), info) ->
    BinaryOp(And,
             nnf_of (UnaryOp(Neg, phi1, info)),
             nnf_of (UnaryOp(Neg, phi2, info)), info')
  | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, nnf_of phi1, nnf_of phi2, info)
  | phi -> failwith ("Unexpected formula " ^ (Convert.PrinterHum.str_of_formula phi) ^ " in nnf_of.")

let rec tseitinize formula =
  let open Proplogic in

  match formula with
  | Formula.True _ -> []
  | Formula.False _ -> [[], []]
  | Formula.Atom (name, _) -> [[], [name]]
  | Formula.UnaryOp (Formula.Neg, Formula.True _, _) -> [[], []]
  | Formula.UnaryOp (Formula.Neg, Formula.False _, _) -> []
  | Formula.UnaryOp (Formula.Neg, Formula.Atom (name, _), _) -> [[name], []]
  | Formula.UnaryOp (Formula.Neg, Formula.UnaryOp (Formula.Neg, formula', _), _) ->
    tseitinize formula'
  | Formula.UnaryOp (Formula.Neg, Formula.BinaryOp (Formula.Or, formula_0, formula_1, _), _) ->
    tseitinize (Formula.mk_neg formula_0 Dummy) @ tseitinize (Formula.mk_neg formula_1 Dummy)
  | Formula.UnaryOp (Formula.Neg, Formula.BinaryOp (Formula.And, formula_0, formula_1, _), _) ->
    tseitinize @@ Formula.mk_or (Formula.mk_neg formula_0 Dummy) (Formula.mk_neg formula_1 Dummy) Dummy
  | Formula.BinaryOp (Formula.And, formula_0, formula_1, _) ->
    tseitinize formula_0 @ tseitinize formula_1
  | Formula.BinaryOp (Formula.Or, formula_0, formula_1, _) ->
    let var_0 = Ident.mk_fresh_pvar () |> function | Ident.Pvar name -> name in
    let var_1 = Ident.mk_fresh_pvar () |> function | Ident.Pvar name -> name in
    let clauses_0 = tseitinize formula_0 in
    let clauses_1 = tseitinize (Formula.mk_neg formula_0 Dummy) in
    let clauses_2 = tseitinize formula_1 in
    let clauses_3 = tseitinize (Formula.mk_neg formula_1 Dummy) in

    [[], [var_0; var_1]] @
    List.map ~f:(fun (negatives, positives) -> (var_0 :: negatives, positives)) clauses_0 @
    List.map ~f:(fun (negatives, positives) -> (negatives, var_0 :: positives)) clauses_1 @
    List.map ~f:(fun (negatives, positives) -> (var_1 :: negatives, positives)) clauses_2 @
    List.map ~f:(fun (negatives, positives) -> (negatives, var_1 :: positives)) clauses_3


let rec rm_outest_forall phi =
  try let _, _, phi, _ = Ast.Logic.Formula.let_bind phi in rm_outest_forall phi with _ -> phi
