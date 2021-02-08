
(* simplified 2-arg versoin of Takeuchi's tarai function *)

let rec tarai2 x y =
  if x <= y
    then y
    else
      tarai2 (tarai2 (x-1) y)
             (tarai2 (y-1) x)

let main x y = let z = tarai2 x y in assert (z <= x || z <= y)

