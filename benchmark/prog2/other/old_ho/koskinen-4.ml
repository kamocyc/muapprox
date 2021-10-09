let ev s = print_string s

let app f x i = f x (fun t -> t - i)

let ha1 _ = ev "ha1"

let ha2 _ = ev "ha2"

let rec walk x f =
  ev "walk";
  if x = 0 then x else walk (f x) f
and run x f =
  ev "run";
  if x = 0 then x else run (f (f x)) f
and life x =
  if read_int () > 0 then (
    ev "p";
    if x<0 then ha1 (app walk x 1)
    else ha2 (app run x 1)
  ) else life x

let () = life (read_int () * 2)

