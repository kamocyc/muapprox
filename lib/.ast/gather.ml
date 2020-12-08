open Core open Core.Poly
open Logic

module Variables = Set.Make(struct
    type t = Ident.tvar * Sort.t
    let compare  (Ident.Tvar x, _) (Ident.Tvar y, _) = compare x y
    let sexp_of_t (Ident.Tvar ident, sort) =
      let sort = match sort with
        | T_bool.SBool -> "bool"
        | T_int.SInt -> "int"
        | T_int.SReal -> "real"
        | _ -> failwith "unknown sort"
      in
      Sexp.List [
        Sexp.Atom ident;
        Sexp.Atom sort;
      ]
    let t_of_sexp = function
      | Sexp.List [Sexp.Atom ident; Sexp.Atom "bool"] -> (Ident.Tvar ident, T_bool.SBool)
      | Sexp.List [Sexp.Atom ident; Sexp.Atom "int"] -> (Ident.Tvar ident, T_int.SInt)
      | Sexp.List [Sexp.Atom ident; Sexp.Atom "real"] -> (Ident.Tvar ident, T_int.SReal)
      | _ -> failwith "unknown sexp"
  end)

let rec free_variables_of_formula phi = let open Formula in
  match phi with
  | Atom (atom, _) -> free_variables_of_atom atom
  | UnaryOp (Neg, phi, _) -> free_variables_of_formula phi
  | BinaryOp (_, phi1, phi2, _) ->
    Variables.union
      (free_variables_of_formula phi1)
      (free_variables_of_formula phi2)
  | Bind (_, params, phi, _) ->
    let fv = free_variables_of_formula phi in
    let bounded = Variables.of_list params in
    Variables.diff fv bounded
  | LetRec (bounded, body, _) ->
    let fv = List.fold_left bounded ~init:Variables.empty ~f:(fun acc (fp, pvar, params, phi) ->
        Variables.union
          acc
          (free_variables_of_pred (Predicate.Fixpoint (fp, pvar, params, phi)))) in
    Variables.union fv (free_variables_of_formula body)

and free_variables_of_atom atom = let open Atom in
  match atom with
  | True _ | False _ -> Variables.empty
  | App (pred, args, _) ->
    Variables.union
      (free_variables_of_pred pred)
      (free_variables_of_args args)

and free_variables_of_pred pred = let open Predicate in
  match pred with
  | Var _ | Psym _ -> Variables.empty
  | Fixpoint (_, _, params, phi) ->
    let vars = free_variables_of_formula phi in
    let params = Variables.of_list params in
    Variables.diff vars params

and free_variables_of_args =
  List.fold_left ~init:Variables.empty ~f:(fun acc arg -> Variables.union acc (free_variables_of_term arg))

and free_variables_of_term term = let open Term in
  match term with
  | Var (ident, sort, _) -> Variables.singleton (ident, sort)
  | FunApp (T_bool.Formula phi, args, _) ->
    Variables.union (free_variables_of_formula phi) (free_variables_of_args args)
  | FunApp (_, args, _) -> free_variables_of_args args


module PredVariables = Set.Make(struct
    type t = Ident.pvar * Sort.t list
    let compare  (Ident.Pvar x, _) (Ident.Pvar y, _) = compare x y
    let sexp_of_t (Ident.Pvar ident, sorts) =
      let sorts = List.map sorts ~f:(function
          | T_int.SInt -> Sexp.Atom "int"
          | T_int.SReal -> Sexp.Atom "real"
          | T_bool.SBool -> Sexp.Atom "bool"
          | _ -> failwith "unknown sort") in
      Sexp.List ((Sexp.Atom ident) :: sorts)
    let t_of_sexp = function
      | Sexp.List (Sexp.Atom ident :: sorts) ->
        let sorts = List.map sorts ~f:(function
            | Sexp.Atom "int" -> T_int.SInt
            | Sexp.Atom "real" -> T_int.SReal
            | Sexp.Atom "bool" -> T_bool.SBool
            | _ -> failwith "unknown sort") in
        Ident.Pvar ident, sorts
      | _ -> failwith "unknown sexp"
  end)


let rec pred_free_variables_of_formula phi = let open Formula in
  match phi with
  | Atom (atom, _) -> pred_free_variables_of_atom atom
  | UnaryOp (Neg, phi, _) -> pred_free_variables_of_formula phi
  | BinaryOp (_, phi1, phi2, _) ->
    PredVariables.union
      (pred_free_variables_of_formula phi1)
      (pred_free_variables_of_formula phi2)
  | Bind _ -> failwith "can not happen"
  | LetRec (bounded, body, _) ->
    let fpv = List.fold_left bounded ~init:PredVariables.empty ~f:(fun acc (fp, pvar, params, phi) ->
        PredVariables.union
          acc
          (pred_free_variables_of_pred (Predicate.Fixpoint (fp, pvar, params, phi)))) in
    let fpv = PredVariables.union fpv (pred_free_variables_of_formula body) in
    let bounded = PredVariables.of_list @@ List.map bounded ~f:(fun (_, pvar, params, _) -> (pvar, AstUtil.sorts_of_params params)) in
    PredVariables.diff fpv bounded


and pred_free_variables_of_atom atom = let open Atom in
  match atom with
  | True _ | False _ -> PredVariables.empty
  | App (pred, args, _) ->
    PredVariables.union
      (pred_free_variables_of_pred pred)
      (pred_free_variables_of_args args)

and pred_free_variables_of_pred pred = let open Predicate in
  match pred with
  | Var (pvar, sorts) -> PredVariables.singleton (pvar, sorts)
  | Psym _ -> PredVariables.empty
  | Fixpoint (_, pvar, params, phi) ->
    let vars = pred_free_variables_of_formula phi in
    let sorts = List.map params ~f:(fun (_, sort) -> sort) in
    PredVariables.diff vars (PredVariables.singleton (pvar, sorts))

and pred_free_variables_of_args =
  List.fold_left ~init:PredVariables.empty ~f:(fun acc arg -> PredVariables.union acc (pred_free_variables_of_term arg))

and pred_free_variables_of_term term = let open Term in
  match term with
  | Var _ -> PredVariables.empty
  | FunApp (_, args, _) -> pred_free_variables_of_args args

