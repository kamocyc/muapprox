open Core open Core.Poly
open Ast.Logic
open Ast
module Sexp = Ppx_sexp_conv_lib.Sexp
module Priority = PrinterHum.Priority
let add_bracket = PrinterHum.add_bracket

let upper_first_letter s =
  (String.uppercase @@ String.sub s ~pos:0 ~len:1) ^ (String.sub s ~pos:1 ~len:(String.length s - 1))

let replace_apos s =
  s
  |> Str.global_replace (Str.regexp "'") "_ap_"
  |> Str.global_replace (Str.regexp "!") "_exc_"
  
let str_of_param' = fun (tvar, _) -> replace_apos @@ Printf.sprintf "%s" (Ident.name_of_tvar tvar)

let str_of_params' params =
  if List.is_empty params then
    ""
  else
    List.map ~f:str_of_param' params
    |> String.concat ~sep:" "

let str_of_fixpoint' = function
  | Predicate.Mu -> "μ"
  | Predicate.Nu -> "ν"

let rec str_of_formula' ?(priority=0) phi = let open Formula in
  match phi with
  | Atom (atom, _) -> str_of_atom' ~priority atom
  | UnaryOp (Neg, phi, _) ->
    add_bracket priority Priority.unary_neg
    @@ Printf.sprintf "not %s" (str_of_formula' ~priority:Priority.unary_neg phi)
  | BinaryOp (And, phi1, phi2, _) ->
    add_bracket priority Priority.binary_and
    @@ Printf.sprintf "%s /\\ %s"
      (str_of_formula' ~priority:Priority.binary_and phi1)
      (str_of_formula' ~priority:Priority.binary_and phi2)
  | BinaryOp (Or, phi1, phi2, _) ->
    add_bracket priority Priority.binary_or
    @@ Printf.sprintf "%s \\/ %s"
      (str_of_formula' ~priority:Priority.binary_or phi1)
      (str_of_formula' ~priority:Priority.binary_or phi2)
  | BinaryOp (Imply, phi1, phi2, _) ->
    add_bracket priority Priority.imply_iff
    @@ Printf.sprintf "%s => %s"
      (str_of_formula' ~priority:Priority.imply_iff phi1)
      (str_of_formula' ~priority:Priority.imply_iff phi2)
  | BinaryOp (Iff, phi1, phi2, _) ->
    add_bracket priority Priority.imply_iff
    @@ Printf.sprintf "%s <=> %s"
      (str_of_formula' ~priority:Priority.imply_iff phi1)
      (str_of_formula' ~priority:Priority.imply_iff phi2)
  | Bind (Forall, params, phi, _) ->
    add_bracket priority Priority.letrec_forall_exists
    @@ Printf.sprintf "%s %s"
      (List.map ~f:(fun p -> "∀" ^ (str_of_param' p) ^ ".") params |> String.concat ~sep:" ")
      (str_of_formula' ~priority:Priority.letrec_forall_exists phi)
  | Bind (Exists, params, phi, _) ->
    add_bracket priority Priority.letrec_forall_exists
    @@ Printf.sprintf "%s %s"
      (List.map ~f:(fun p -> "∃" ^ (str_of_param' p) ^ ".") params |> String.concat ~sep:" ")
      (str_of_formula' ~priority:Priority.letrec_forall_exists phi)
  | LetRec _ -> failwith "LetRec"
    (* add_bracket priority Priority.letrec_forall_exists
    @@ Printf.sprintf "let rec %s in %s"
      (String.concat ~sep:" and "
         (List.map ~f:(fun (fix, pvar, bounds, body) ->
              let var_names =
                if bounds = [] then
                  ["()"]
                else
                  List.map ~f:(fun (tvar, _) -> Ident.name_of_tvar tvar) bounds
              in
              Printf.sprintf "%s %s =%s %s"
                (Ident.name_of_pvar pvar)
                (String.concat ~sep:" " var_names)
                (str_of_fixpoint fix)
                (str_of_formula ~priority:0 body)
            ) funcs)
      )
      (str_of_formula ~priority:0 body) *)

and str_of_atom' ?(priority=0) atom = let open Atom in
  match atom with
  | True _ -> "true"
  | False _ -> "false"
  | App (Predicate.Psym (T_bool.Eq as op), [t1; t2], _)
  | App (Predicate.Psym (T_bool.Neq as op), [t1; t2], _)
  | App (Predicate.Psym (T_int.Leq as op), [t1; t2], _)
  | App (Predicate.Psym (T_int.Geq as op), [t1; t2], _)
  | App (Predicate.Psym (T_int.Lt as op), [t1; t2], _)
  | App (Predicate.Psym (T_int.Gt as op), [t1; t2], _) ->
    add_bracket priority Priority.eq_neq_lt_leq_gt_geq
    @@ Printf.sprintf "%s %s %s"
      (str_of_term' Priority.eq_neq_lt_leq_gt_geq t1)
      (str_of_predsym' op)
      (str_of_term' Priority.eq_neq_lt_leq_gt_geq t2)
  | App (pred, args, _) ->
    if List.length args = 0 then
      str_of_pred' pred
    else
      add_bracket priority Priority.funapp
      @@ Printf.sprintf "%s %s"
        (str_of_pred' pred)
        (
          List.map ~f:(fun arg -> str_of_term' Priority.funapp arg) args
          |> String.concat ~sep:" "
        )
and str_of_pred' pred = let open Predicate in
  match pred with
  | Var (Ident.Pvar ident, _) -> upper_first_letter ident
  | Psym sym -> str_of_predsym' sym
  | Fixpoint (fp, Ident.Pvar pident, params, phi) ->
    Printf.sprintf "(%s%s(%s). %s)"
      (str_of_fixpoint' fp)
      pident
      (str_of_params' params)
      (str_of_formula' ~priority:0 phi)
and str_of_term' priority = function
  | Term.Var (Ident.Tvar ident, T_int.SUnrefInt, _) -> "*"^ident
  | Term.Var (Ident.Tvar ident, T_int.SRefInt, _) -> "&"^ident
  | Term.Var (Ident.Tvar ident, _, _) -> ident
  | Term.FunApp (T_bool.Bool atom, [], _) ->
    str_of_atom' ~priority:Priority.atom atom
  | Term.FunApp (T_bool.Formula phi, [], _) ->
    str_of_formula' ~priority:Priority.atom phi
  | Term.FunApp (T_bool.IfThenElse, [cond; then_; else_], _) ->
    Printf.sprintf "(if %s then %s else %s)"
      (str_of_term' 0 cond)
      (str_of_term' 0 then_)
      (str_of_term' 0 else_)
  | Term.FunApp (T_int.Int n, [], _) -> Bigint.to_string_hum n
  | Term.FunApp (T_int.Real str, [], _) -> str
  | Term.FunApp (T_int.Add as op, [t1; t2], _)
  | Term.FunApp (T_int.Sub as op, [t1; t2], _) ->
    add_bracket priority Priority.add_sub
    @@ Printf.sprintf "%s %s %s"
      (str_of_term' Priority.add_sub t1)
      (str_of_funsym' op)
      (str_of_term' Priority.add_sub t2)
  | Term.FunApp (T_int.Mult as op, [t1; t2], _)
  | Term.FunApp (T_int.Div as op, [t1; t2], _)
  | Term.FunApp (T_int.Mod as op, [t1; t2], _) ->
    add_bracket priority Priority.mult_div
    @@ Printf.sprintf "%s %s %s"
      (str_of_term' Priority.mult_div t1)
      (str_of_funsym' op)
      (str_of_term' Priority.mult_div t2)
  | Term.FunApp (T_int.UnaryNeg, [t], _) ->
    add_bracket priority Priority.arith_neg
    @@ Printf.sprintf "-%s" (str_of_term' Priority.arith_neg t)
  | Term.FunApp (FunCall funname, args, _) ->
    add_bracket priority Priority.funapp
    @@ Printf.sprintf "%s %s" funname (List.map ~f:(str_of_term' Priority.funapp) args |> String.concat ~sep:" ")
  | _ -> failwith "unknown function applicataion"
and str_of_funsym' = function
  | T_int.Add -> "+"
  | T_int.Sub -> "-"
  | T_int.Mult -> "*"
  | T_int.Div -> "/"
  | T_int.Mod -> "mod"
  | T_int.UnaryNeg -> "-"
  | _ -> failwith "unknown function symbol"
and str_of_predsym' = function
  | T_bool.Eq -> "="
  | T_bool.Neq -> "!="
  | T_int.Leq -> "<="
  | T_int.Geq -> ">="
  | T_int.Lt -> "<"
  | T_int.Gt -> ">"
  | _ -> failwith "unknown pred symbol"

let str_of_formula'' ?(priority=0) phi =
  replace_apos @@ str_of_formula' ~priority:priority phi

let str_of_func' func =
  let fix, Ident.Pvar pvar_name, args, body = Hes.HesLogic.let_function func in
  Printf.sprintf
    "%s%s =%s %s."
    (upper_first_letter pvar_name)
    (if List.length args > 0 then " "^ str_of_params' args else "")
    (str_of_fixpoint' fix)
    (str_of_formula'' body)

let str_of_func_list' funcs =
  List.map ~f:str_of_func' funcs
  |> String.concat ~sep:"\n"

let str_of_hes' hes =
  let funcs, entry = Hes.HesLogic.let_hes hes in
  "%HES\n" ^
  "Sentry =ν " ^ (str_of_formula'' entry) ^ ".\n"
  ^ (replace_apos @@ str_of_func_list' funcs)