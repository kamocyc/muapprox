open Core open Core.Poly
open Ast.Logic
open Ast
open Convert


type t = (Ident.tvar * Term.t) list

let str_of = function
  | [] -> "[]"
  | (Ident.Tvar ident, term) :: tl ->
    let mk_ass ident term = Printf.sprintf "%s -> %s" ident (PrinterHum.str_of_term term) in
    let inner =
      List.fold_left tl ~init:(mk_ass ident term) ~f:(fun acc (Ident.Tvar ident, term) ->
          acc ^ ", " ^ (mk_ass ident term))
    in
    "[" ^ inner ^ "]"

module Assignment = Set.Make(struct
    type t = Ident.tvar * Term.t
    let compare (Ident.Tvar x, _) (Ident.Tvar y, _) = compare x y
    let sexp_of_t (Ident.Tvar ident, term) =
      let term = Printer.sexp_of_term term in
      Sexp.List [Sexp.Atom ident; term]
    let t_of_sexp = function
      | Sexp.List [Sexp.Atom ident; term] -> begin
          match Parser.term_of_sexp term with
          | Ok(term) -> (Ident.Tvar ident, term)
          | Error msg -> failwith ("invalid term sexp: " ^ msg)
        end
      | _ -> failwith "invalid sexp"
  end)
(*
let rec gather acc n (cs:Constraint.t list) =
  let vars = Constraint.variables_of cs in
  let vars = Gather.Variables.to_list vars in
  let sample = List.map vars ~f:(fun (var, sort) ->
      match sort with
      | T_bool.SBool ->
        let atom =
          if Random.bool () then Atom.mk_true Dummy
          else Atom.mk_false Dummy in
        (var, T_bool.mk_bool atom Dummy)
      | T_int.SInt ->
        (var, T_int.mk_int (Random.int 1000) Dummy)
      | _ -> failwith "unknown sort"
    ) in
  if Constraint.subst sample cs |> Constraint.is_valid then
    gather (sample :: acc) (n-1) cs
  else
    gather acc n cs

let gather = gather [] 10 *)

let sample_of_model model =
  let decls = Z3.Model.get_const_decls model in
  List.map decls ~f:(fun decl ->
      let ident = Ident.Tvar (Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl) in
      let expr = match Z3.Model.get_const_interp model decl with
        | None -> failwith "can not happen"
        | Some(e) -> e
      in
      let term = Smt.Z3interface.term_of Env.empty Env.empty expr in
      (ident, term)
    )
let str_of_samples =
  List.fold_left ~init:"" ~f:(fun acc sample-> acc ^ "\n" ^ str_of sample)
