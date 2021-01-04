
let () = 
  let is_option text = text = "--from-hes" || text = "--from-in" in
  let argv = Array.to_list Sys.argv in
  if List.length argv <> 3 || List.nth argv 1 |> is_option |> not then failwith "Usage: PROGRAM.exe (--from-hes | --from-in) file_path";
  match argv with
  | [_ ; "--from-hes"; path1] -> begin
    let phi1 = Muapprox.parse path1 true in
    let path2 = Filename.remove_extension path1 ^ ".in" in
    ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 false phi1
  end
  | [_; "--from-in"; path1] -> begin
    let phi1 = Muapprox.parse path1 false in
    let path2 = Filename.remove_extension path1 ^ ".hes" in
    ignore @@ Muapprox.Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:path2 phi1
  end
  | _ -> assert false