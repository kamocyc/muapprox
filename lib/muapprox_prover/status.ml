(* exception Timeout
exception Error of string *)

type t =
  | Valid
  | Invalid
  | Unknown
  | Fail

let flip = function
  | Valid -> Invalid
  | Invalid -> Valid
  | Unknown -> Unknown
  | Fail -> Fail

let string_of = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Fail -> "fail"

let of_string str = 
  let str = String.lowercase_ascii str in
  match str with
  | "fail" -> Fail
  | "valid" -> Valid
  | "invalid" -> Invalid
  | "unknown" -> Unknown
  | _ -> failwith @@ "Illegal status string (" ^ str ^ ")"

exception Timeout