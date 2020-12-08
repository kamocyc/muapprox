
(*
  entrypoint should be of the form:
    Forall ... Forall <formula>
  <formula> and t's formula don't contain nu, mu predicates
  A body of func should not have negative occurence of predicate application.
  It doesn't matter even if func list does not have order unlike the definition in POPL '17.
*)
open Ast
open Ast.Logic

type entrypoint = Formula.t
type func = Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t
type hes = Hes of func list * entrypoint

val get_functions: hes -> func list
val get_entrypoint: hes -> entrypoint
val get_fixpoint_of_function: func -> Predicate.fixpoint
val get_pvar_of_function: func -> Ident.pvar
val get_args_of_function: func -> (Ident.tvar * Sort.t) list
val get_body_of_function: func -> Formula.t
val get_size: hes -> int

val get_pvars_of_functions: func list -> Ident.pvar list

val let_hes: hes -> func list * entrypoint
val let_function: func -> Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t

val get_depth_ht: hes -> (Ident.pvar, int) Hashtbl.t

val is_onlymu: hes -> bool
val is_onlynu: hes -> bool
val mk_hes: func list -> entrypoint -> hes
val mk_func: Predicate.fixpoint -> Ident.pvar -> (Ident.tvar * Sort.t) list -> Formula.t -> func
