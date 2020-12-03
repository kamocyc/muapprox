let rec sum x k = ((x > 0) || (k 0)) && ((x <= 0) || sum (x - 1) (fun m -> k (m + x)))
let main x = sum x (fun y -> true)

