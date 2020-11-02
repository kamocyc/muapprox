(*
USED: PEPM2013 as risers
FROM: Example of [Ong and Ramsay, 2011]
*)

let rec make_list m =
  if m <= 0
  then []
  else (Random.int 0) :: make_list (m-1)

let rec risers xs =
  let risersElse x = function
      [] -> assert false
    | s::ss -> [x]::s::ss
  in
  let risersThen x = function
      [] -> assert false
    | s::ss -> (x::s)::ss
  in
  match xs with
    [] -> []
  | [x] -> [[x]]
  | x::y::etc ->
      if x < y
      then risersThen x (risers (y::etc))
      else risersElse x (risers (y::etc))

let main m = risers (make_list m)
