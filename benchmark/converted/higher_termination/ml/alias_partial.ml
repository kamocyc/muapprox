let rec f x = if x > 0 then f (x - 1) else lambda
and lambda x = x + 1
let g = f 1
let main (u:unit) = g 2
