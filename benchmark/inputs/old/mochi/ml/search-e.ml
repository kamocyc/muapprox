type option = None | Some of int

let rec exists test f n m =
  if n < m
  then
    if test (f n)
    then Some n
    else exists test f (n+1) m
  else
    None

let mult3 n = 3 * n

let main n m =
  let test x = x = m in
    match exists test mult3 0 n with
        None -> ()
      | Some x -> assert (0 < x && x < n)
