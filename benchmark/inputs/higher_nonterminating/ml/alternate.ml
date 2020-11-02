let rec f g h z = let x = read_int () in if x>0 then g (f h g) else h (f h g)
let proceed u = u ()
let halt u = ()
let main () = f proceed halt ()
