
let dprint strgen =
  let config = !Global.config in
  if config.verbose then
    (print_endline (strgen ());
     flush stdout)
  else
    ()

let print str = dprint (fun () -> str)
