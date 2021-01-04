open Fptprover
open Ast.Logic
open Hes

val solve_formula: Formula.t -> (Status.t->unit)->unit
val solve_hes: HesLogic.hes -> (Status.t->unit)->unit
val solve: HesLogic.hes -> (Status.t->unit)->unit
val solve_onlyforall: int -> HesLogic.hes -> Status.t Async.Deferred.t
(* val solve_onlyexists: int -> HesLogic.hes -> (Status.t->unit)->unit *)
