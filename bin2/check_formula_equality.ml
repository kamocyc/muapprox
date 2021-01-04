
let () = 
  let argv = Array.to_list Sys.argv in
  if List.length argv <> 3 then failwith "Usage: PROGRAM.exe file1 file2";
  match argv with
  | [_; path1; path2] -> begin
    let phi1 = Muapprox.parse path1 true in
    let phi2 = Muapprox.parse path2 true in
    let phi1' = Muapprox.assign_serial_to_vars_hes phi1 in
    let phi2' = Muapprox.assign_serial_to_vars_hes phi2 in
    let res, error_path = Muapprox.check_equal_hes phi1' phi2' in
    (if res then
      print_endline "(func) Equal"
    else
      print_endline ("(func) Not equal: " ^ error_path))
  end
  | _ -> assert false