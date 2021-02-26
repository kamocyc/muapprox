let rec fib_CPS_nonterm n k =
  if n = 0 || n = 1 then k 1
  else
    let pn = n - 1 in
    let ppn = n - 2 in
    fib_CPS_nonterm pn (cont1 ppn k)
and cont1 ppn (k:int->int) a = fib_CPS_nonterm ppn (cont2 a k)
and cont2 a (k:int->int) b = k (a + b)
let id (n:int) = n
let main () =
  let r = read_int () in
  fib_CPS_nonterm r id

