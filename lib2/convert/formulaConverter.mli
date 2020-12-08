open Ast.Logic

val elim_fv_with_forall: Formula.t -> Formula.t
val elim_fv_with_exists: Formula.t -> Formula.t
val elim_fv_with_binder: Formula.binder -> Formula.t -> Formula.t
val move_quantifiers_to_front: Formula.t -> Formula.t
val into_cnf_naive: Formula.t -> Formula.t
