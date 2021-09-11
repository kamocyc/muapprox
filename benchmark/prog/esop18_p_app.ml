let event x = print_string x

let rec fb x = if x > 0 then (event "a"; app fa (x-1)) else (event "b"; app fb 5)
and fa x = if x > 0 then (event "a"; app fa (x-1)) else (event "b"; app fb 5)
and app h x = h x

let () = fb 5