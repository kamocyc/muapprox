let rec mc91 n =
  if n > 100 then
    n - 10
  else
    mc91 (mc91 (n + 11))
in mc91 (Random.int 0)
