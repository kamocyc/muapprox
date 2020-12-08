open Ast.Logic
open CSyntax

val from_file: string -> (Formula.t BuchiAutomaton.t, string) result

val parse: string -> (Formula.t BuchiAutomaton.t, string) result
