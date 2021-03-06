exception NotPositive

let rec fact n =
  if n <= 0
  then
    raise NotPositive
  else
    try
      n * fact (n-1)
    with NotPositive -> 1

let main n =
  try
    fact n
  with NotPositive when n <= 0 -> 0
