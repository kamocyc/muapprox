(* simple parser of fixpoint logic for debug *)

open Core open Core.Poly
open Ast
open Ast.Logic
open Parsexp
module Sexp = Ppx_sexp_conv_lib.Sexp

let binop_of_sexp binop = let open Formula in
  match binop with
  | Sexp.Atom "and" | Sexp.Atom "And" -> Ok And
  | Sexp.Atom "or" | Sexp.Atom "Or" -> Ok Or
  | Sexp.Atom "imply" | Sexp.Atom "Imply" -> Ok Imply
  | Sexp.Atom "iff" | Sexp.Atom "Iff" -> Ok Iff
  | _ -> Error (Printf.sprintf "invalid binop: %s" @@ Sexp.to_string binop)

let sort_of_str = function
  | "bool" -> Ok(T_bool.SBool)
  | "int" -> Ok(T_int.SInt)
  | "real" -> Ok(T_int.SReal)
  | str -> Error (Printf.sprintf "invalid sort: %s" str)

let rec formula_of_sexp phi = let open Formula in
  match phi with
  | Sexp.List [Sexp.Atom "atom"; atom] ->
    atom_of_sexp atom
    |> Util.Result.map_ok (fun atom -> mk_atom atom Dummy)

  | Sexp.List [Sexp.Atom "not"; phi] ->
    formula_of_sexp phi
    |> Util.Result.map_ok (fun phi -> mk_neg phi Dummy)

  | Sexp.List [Sexp.Atom "forall"; Sexp.List params; phi]
  | Sexp.List [Sexp.Atom "Forall"; Sexp.List params; phi] -> begin
      match params_of_sexp params, formula_of_sexp phi with
      | Ok(params), Ok(phi) -> Ok(mk_forall params phi Dummy)
      | Error(x), _ | _, Error (x) -> Error x
    end

  | Sexp.List [Sexp.Atom "exists"; Sexp.List params; phi]
  | Sexp.List [Sexp.Atom "Exists"; Sexp.List params; phi] -> begin
      match params_of_sexp params, formula_of_sexp phi with
      | Ok(params), Ok(phi) -> Ok(mk_exists params phi Dummy)
      | Error (x), _ | _, Error (x) -> Error x
    end

  | Sexp.List [Sexp.Atom "letrec"; Sexp.List bounded; phi] -> begin
      let bounded = List.fold_left bounded ~init:[] ~f:(fun acc x ->
          match pred_of_sexp x with
          | Ok(Predicate.Fixpoint (fp, pvar, params, phi)) -> (Ok(fp, pvar, params, phi)) :: acc
          | _ -> [Error (Printf.sprintf "invalid letrec: %s" @@ Sexp.to_string x)]) in
      match (Util.Result.collect_from_list bounded), (formula_of_sexp phi) with
      | Ok (bounded), Ok(phi) -> Ok (mk_letrec bounded phi Dummy)
      | Error x, _ | _, Error x -> Error x
    end

  | Sexp.List [op; phi1; phi2] -> begin
      match binop_of_sexp op, formula_of_sexp phi1, formula_of_sexp phi2 with
      | Ok(op), Ok(phi1), Ok(phi2) -> Ok(mk_binop op phi1 phi2 Dummy)
      | Error (x), _, _ | _, Error (x), _ | _, _, Error(x) ->
        Error x
    end

  | phi -> Error (Printf.sprintf "invalid formula: %s" @@ Sexp.to_string phi)

and atom_of_sexp atom = let open Atom in
  match atom with
  | Sexp.Atom "true" -> Ok(mk_true Dummy)
  | Sexp.Atom "false" -> Ok(mk_false Dummy)
  | Sexp.List [Sexp.Atom "predapp"; pred; Sexp.List args] -> begin
      match pred_of_sexp pred, args_of_sexp args with
      | Ok(pred), Ok(args) -> Ok(mk_app pred args Dummy)
      | Error(x), _ | _, Error (x) -> Error x
    end
  | atom -> Error (Printf.sprintf "invalid atom: %s" @@ Sexp.to_string atom)

and pred_sym_of_str = function
  | "eq" -> Ok(T_bool.Eq)
  | "neq" -> Ok(T_bool.Neq)
  | "leq" -> Ok(T_int.Leq)
  | "geq" -> Ok(T_int.Geq)
  | "lt" -> Ok(T_int.Lt)
  | "gt" -> Ok(T_int.Gt)
  | x -> Error ("invalid predicate symbol: " ^ x)

and fun_sym_of_sexp = function
  | Sexp.List [Sexp.Atom "boolean"; atom] ->
    atom_of_sexp atom
    |> Util.Result.map_ok (fun atom -> T_bool.Bool atom)
  | Sexp.List [Sexp.Atom "integer"; Sexp.Atom n] -> Ok(T_int.Int (Bigint.of_string n))
  | Sexp.Atom "add" -> Ok(T_int.Add)
  | Sexp.Atom "sub" -> Ok(T_int.Sub)
  | Sexp.Atom "mult" -> Ok(T_int.Mult)
  | Sexp.Atom "div" -> Ok(T_int.Div)
  | Sexp.Atom "mod" -> Ok(T_int.Mod)
  | Sexp.Atom "neg" -> Ok(T_int.UnaryNeg)
  | x -> Error ("invalid function symbol : " ^ (Sexp.to_string_hum x))

and pred_of_sexp pred = let open Predicate in
  match pred with
  | Sexp.Atom sym ->
    pred_sym_of_str sym
    |> Util.Result.map_ok (fun sym -> Psym sym)
  | Sexp.List [Sexp.Atom ident; Sexp.List sorts] ->
    sorts_of_sexp sorts
    |> Util.Result.map_ok (fun sorts -> Var (Ident.Pvar ident, sorts))
  | Sexp.List [Sexp.Atom fp; Sexp.Atom ident; Sexp.List params; phi] when fp = "mu" || fp = "nu" -> begin
      let fp = if fp = "mu" then Mu else Nu in
      match params_of_sexp params, formula_of_sexp phi with
      | Ok(params), Ok(phi) ->
        Ok(Fixpoint (fp, Ident.Pvar ident, params, phi))
      | Error (x), _ | _, Error(x) -> Error x
    end
  | _ -> Error (Printf.sprintf "invalid predicate: %s" @@ Sexp.to_string pred)

and params_of_sexp = function
  | [] -> Ok([])
  | (Sexp.List [Sexp.Atom ident; Sexp.Atom sort]) :: xs -> begin
      match sort_of_str sort, params_of_sexp xs with
      | Ok(sort), Ok(tail) ->
        Ok((Ident.Tvar ident, sort) :: tail)
      | Error x, _ | _, Error x -> Error x
    end
  | t :: _ -> Error (Printf.sprintf "invalid params: %s" @@ Sexp.to_string t)

and args_of_sexp = function
  | [] -> Ok([])
  | x :: xs -> begin
      match term_of_sexp x, args_of_sexp xs with
      | Ok(t), Ok(ts) -> Ok(t :: ts)
      | Error x, _ | _, Error x -> Error x
    end

and sorts_of_sexp = function
  | [] -> Ok([])
  | (Sexp.Atom sort) :: xs -> begin
      match sort_of_str sort, sorts_of_sexp xs with
      | Ok(sort), Ok(xs) -> Ok (sort :: xs)
      | Error x, _ | _, Error x -> Error x
    end
  | t :: _ -> Error (Printf.sprintf "invalid sort: %s" @@ Sexp.to_string t)

and term_of_sexp t = let open Term in
  match t with
  | Sexp.List [Sexp.Atom ident; Sexp.Atom sort] ->
    sort_of_str sort
    |> Util.Result.map_ok (fun sort -> mk_var (Ident.Tvar ident) sort Dummy)
  | Sexp.List [Sexp.Atom "funapp"; sym; Sexp.List args] -> begin
      match fun_sym_of_sexp sym, args_of_sexp args with
      | Ok(sym), Ok(args) -> Ok(mk_funapp sym args Dummy)
      | Error x, _ | _, Error x -> Error x
    end
  | Sexp.List [Sexp.Atom "if-then-else"; cond; then_; else_] -> begin
      let cond = term_of_sexp cond in
      let then_ = term_of_sexp then_ in
      let else_ = term_of_sexp else_ in
      match cond, then_, else_ with
      | Ok(cond), Ok(then_), Ok(else_) ->
        Ok(mk_funapp T_bool.IfThenElse [cond; then_; else_] Dummy)
      | Error x, _, _ | _, Error x , _ | _, _, Error x -> Error x
    end
  | Sexp.Atom n ->
    (try Ok(mk_funapp (T_int.Int (Bigint.of_string n)) [] Dummy)
     with Failure _ ->
       Error (Printf.sprintf "invalid term: %s" @@ Sexp.to_string t))
  | t ->
    Error (Printf.sprintf "invalid term: %s" @@ Sexp.to_string t)


let formula_of_str str =
  match Single.parse_string str with
  | Ok sexp -> formula_of_sexp sexp
  | Error _ -> Error ("invalid Sexp: " ^ str)

let from_file filename = formula_of_str (In_channel.read_all filename)

