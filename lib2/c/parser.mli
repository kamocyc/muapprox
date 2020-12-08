open Hes

val from_cctl_file: string -> (HesLogic.hes, string) result

val from_cltl_file: string -> (HesLogic.hes, string) result

val parse_cctl: string -> (HesLogic.hes, string) result

val parse_cltl: string -> (HesLogic.hes, string) result
