open Ast
open Ast.Logic
open Hes

val move_quantifiers_to_front: HesLogic.hes -> HesLogic.hes
val simplify: HesLogic.hes -> HesLogic.hes
val get_dual_hes: HesLogic.hes -> HesLogic.hes
val get_greatest_approx_hes: ?range:int -> HesLogic.hes -> HesLogic.hes
val encode_top_exists: ?range:int -> HesLogic.hes -> HesLogic.hes
val encode_body_exists: ?range:int -> HesLogic.hes -> HesLogic.hes

val replace_app: (Formula.t -> Formula.t) -> Formula.t -> Formula.t
val replace_app_add: Formula.t -> Term.t -> Sort.t -> Formula.t
val iter_app: (Ident.pvar -> Term.t list -> unit) -> Formula.t -> unit
val elim_mu_from_funcs_with_rec: HesLogic.func list -> Ast.Ident.tvar -> HesLogic.func list
val get_next_funcs: Formula.t -> Ast.Ident.pvar list

val formula_of_hes: HesLogic.hes -> Formula.t
val hes_of_formula: Formula.t -> HesLogic.hes

val str_of_func: HesLogic.func -> string
val str_of_hes: HesLogic.hes -> string
val str_of_hes': HesLogic.hes -> string

val is_onlyforall: HesLogic.hes -> bool
val is_onlyexists: HesLogic.hes -> bool
val is_noquantifier: HesLogic.hes -> bool

val elim_fv_with_forall: HesLogic.hes -> HesLogic.hes
