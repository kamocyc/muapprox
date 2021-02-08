let rec make_list m =
  if m <= 0
  then []
  else (Random.int 0) :: make_list (m-1)

let risersElse x = function
    [] -> assert false
  | s::ss -> [x]::s::ss

let risersThen x = function
    [] -> assert false
  | s::ss -> (x::s)::ss

let rec risers = function
    [] -> []
  | [x] -> [[x]]
  | x::y::etc ->
      if x < y
      then risersThen x (risers (y::etc))
      else risersElse x (risers (y::etc))

let main m = risers (make_list m)
