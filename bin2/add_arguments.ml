open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)


let main path1 debug simplified_type =
  let is_hes = Muapprox.check_format path1 "auto" in
  let phi1 = Muapprox.parse path1 is_hes in
  let path2 = map_file_path path1 (fun (a, b, c) -> (a, b ^ "_infer_flag_2", c)) in
  let phi1,  _, _ =
    Muapprox.Manipulate.Add_arguments_definition.output_debug_info := debug;
    Muapprox.Manipulate.Add_arguments_definition.simplified_type := simplified_type;
    Muapprox.Manipulate.Add_arguments_infer_partial_application.infer phi1 1 0 true
  in
  let phi1 = Muapprox.abbrev_variable_numbers_hes phi1 in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi1;
  print_endline @@ "saved to " ^ path2


let command =
  Command.basic
    ~summary:"Add arguments test"
    Command.Let_syntax.(
      let%map_open
          path = anon ("path" %: string)
      and debug = flag "--debug" no_arg ~doc:"Output debug info"
      and simplified_type = flag "--simplified-type" no_arg ~doc:"Show types as simplified format"
      in
      (fun () -> main path debug simplified_type)
    )

let () = Command.run command
