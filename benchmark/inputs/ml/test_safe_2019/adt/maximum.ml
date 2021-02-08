
let rec maximum = function
  | [] -> assert false
  | [x] -> x
  | x::l ->
      let y = maximum l in
      if x > y
        then x
        else y

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let main l = if length l > 0 then let _ = maximum l in ()

