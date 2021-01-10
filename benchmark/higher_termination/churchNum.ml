let rec succ (m:(int->int)->int->int) (s:int->int) z = m s (s z)
let rec id (x:int) = x
let rec two (f:((int->int)->int->int)->(int->int)->int->int) z = f (f z)
let rec zero (f:int->int) (z:int) = z
let main (u:unit) = two succ zero id 0
