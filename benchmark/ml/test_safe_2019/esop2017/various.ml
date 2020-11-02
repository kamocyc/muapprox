let main n =
  let rec sum n =
    if n <= 0
    then 0
    else n + sum (n-1)
  in
  assert (n <= sum n)


let main n =
  let rec mult n m =
    if n <= 0 || m <= 0
    then 0
    else n + mult n (m-1)
  in
  assert (n <= mult n n);
  main n

let main n =
  let rec mc91 x =
    if x > 100
    then x - 10
    else mc91 (mc91 (x + 11))
  in
  if n <= 101 then assert (mc91 n = 91);
  main n
