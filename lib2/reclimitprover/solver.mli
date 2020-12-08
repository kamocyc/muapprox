open Fptprover
open Ast.Logic
open Hes

val solve_formula: Formula.t -> Status.t
val solve_hes: HesLogic.hes -> Status.t
val solve: HesLogic.hes -> Status.t
val solve_onlyforall: int -> HesLogic.hes -> Status.t
val solve_onlyexists: int -> HesLogic.hes -> Status.t
