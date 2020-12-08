open Ast
open Ast.Logic

type entrypoint = Formula.t
type func = (Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t)
type hes = Hes of func list * entrypoint

let get_functions = function Hes (funs, _) -> funs
let get_entrypoint = function Hes (_, entry) -> entry
let get_fixpoint_of_function = function (fix, _, _, _) -> fix
let get_pvar_of_function = function (_, pvar, _, _) -> pvar
let get_args_of_function = function (_, _, args, _) -> args
let get_body_of_function = function (_, _, _, body) -> body
let get_size = function Hes (funs, _) -> List.length funs

let get_pvars_of_functions funcs = List.map get_pvar_of_function funcs

let let_hes = function Hes (funcs, entry) -> (funcs, entry)
let let_function = function func -> func

let get_depth_ht = function Hes (funcs, _) ->
  let res = Hashtbl.create (List.length funcs) in
  List.iteri
    (fun i func ->
       let _, pvar, _, _ = let_function func in
       Hashtbl.add res pvar i
    )
    funcs;
  res

let is_onlymu = function Hes (funs, _) -> List.for_all (fun (fixpoint, _, _, _) -> fixpoint = Predicate.Mu) funs
let is_onlynu = function Hes (funs, _) -> List.for_all (fun (fixpoint, _, _, _) -> fixpoint = Predicate.Nu) funs

let mk_hes funcs entry = Hes (funcs, entry)
let mk_func fix pvar args formula = (fix, pvar, args, formula)
