open Core

let main path1 path2 = 
  let phi1 = Muapprox.parse path1 in
  let phi2 = Muapprox.parse path2 in
  let phi1' = Muapprox.assign_serial_to_vars_hes phi1 in
  let phi2' = Muapprox.assign_serial_to_vars_hes phi2 in
  let phi1' = Hflmc2_syntax.Hflz.merge_entry_rule phi1' in
  let phi2' = Hflmc2_syntax.Hflz.merge_entry_rule phi2' in
  let res, error_path = Muapprox.check_equal_hes phi1' phi2' in
  (if res then
    print_endline "(func) Equal"
  else
    print_endline ("(func) Not equal: " ^ error_path))
  
let command =
  Command.basic
    ~summary:"Check whether two hes files have differences"
    Command.Let_syntax.(
      let%map_open
          path1 = anon ("path1" %: string)
      and path2 = anon ("path2" %: string)
      in
      (fun () -> main path1 path2)
    )

let () = Command.run command
