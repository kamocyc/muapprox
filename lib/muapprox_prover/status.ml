(* exception Timeout
exception Error of string *)

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

let of_string str = 
  let str = String.lowercase_ascii str in
  match str with
  | "valid" -> Valid
  | "invalid" -> Invalid
  | "unknown" -> Unknown
  | "sat" -> Sat
  | "unsat" -> UnSat
  | _ -> failwith @@ "Illegal status string (" ^ str ^ ")"

exception Timeout