let rec add x y = if y <= 0 then x else 1 + add x (y-1)
let rec sum x = if x <= 0 then 0 else add x (sum (x-1))
let main n = assert (0 <= sum n)
