
(** Ordinals *)
module Ordinal = struct
  type t = int
  let make n = n

  let string_of n =
    if n = 11 || n = 12 || n = 13 then
      Printf.sprintf "%dth" n
    else
      Printf.sprintf (match n mod 10 with
          | 1 -> "%dst"
          | 2 -> "%dnd"
          | 3 -> "%drd"
          | _ -> "%dth") n
end

