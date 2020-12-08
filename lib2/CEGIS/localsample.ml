open Core open Core.Poly
open Ast.Logic
open Ast
open Convert

type t = Formula.t

let str_of = PrinterHum.str_of_formula

let str_of_samples samples =
  let rec inner acc = function
    | []    -> acc
    | t::ls -> inner (str_of t ^ ";\n" ^ acc) ls
  in "[\n" ^ (inner "" samples) ^ "]"

let decl_to_tvar decl =
  Ident.Tvar (Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl)

let peel_opt = function
  | None -> assert false
  | Some e -> e

let filter (Ident.Tvar ident,_) =
  String.substr_index ~pattern:"paramvar" ident = None

(* Z3.Model.model -> Constraint.t -> Candidate.t -> LocalSample.t *)
let sample_of_model model c template =
  let decls = Z3.Model.get_const_decls model in
  let map =
    List.map decls
      ~f:(fun decl ->
          let ident = decl_to_tvar decl in
          let expr = peel_opt @@ Z3.Model.get_const_interp model decl in
          let term = Smt.Z3interface.term_of Env.empty Env.empty expr in
          (ident, term)
        ) in
  let map = List.filter ~f:filter map |> Map.Poly.of_alist_exn in
  List.fold_left template ~init:c
    ~f:(fun acc t -> Constraint.subst_pred_ acc t)
  |> Constraint.formula_of_
  |> Formula.subst map
