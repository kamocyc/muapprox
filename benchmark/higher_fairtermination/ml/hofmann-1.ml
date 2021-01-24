
let rec f () = eventA ()
and eventA () = eventB ()
and eventB () = f ()

let main () = f()