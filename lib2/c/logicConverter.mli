open CSyntax
open Ast.Logic

val ba_of_ltl: Ltl.t -> Formula.t BuchiAutomaton.t

val hmes_of_ba: Formula.t BuchiAutomaton.t -> HMES.t
