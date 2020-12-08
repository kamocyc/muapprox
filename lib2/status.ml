exception Timeout
exception Error of string

type t =
  | Valid
  | Invalid
  | Unknown
  | Sat
  | UnSat

let flip = function
  | Valid -> Invalid
  | Invalid -> Valid
  | Unknown -> Unknown
  | Sat   -> UnSat
  | UnSat -> Sat

let string_of = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Sat -> "sat"
  | UnSat -> "unsat"
