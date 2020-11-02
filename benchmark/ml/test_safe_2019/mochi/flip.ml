let sub x y = x - y
let flip f x y = f y x
let main x y = assert (flip (flip sub) x y = x - y)
