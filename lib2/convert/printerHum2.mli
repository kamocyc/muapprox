open Ast
open Ast.Logic

val str_of_params' : (Ident.tvar * 'a) list -> string
val str_of_formula'' : ?priority:int -> Formula.t -> string
val str_of_fixpoint' : Predicate.fixpoint -> string
val str_of_hes' : Hes.HesLogic.hes -> string
