open Core

let main path1 from show_forall =
  let path2 =
    match from with
    | "hes" ->
      let phi1 = Muapprox.parse path1 true in
      let path2 = Stdlib.Filename.remove_extension path1 ^ ".in" in
      Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 show_forall phi1
    | "in" ->
      let phi1 = Muapprox.parse path1 false in
      let path2 = Stdlib.Filename.remove_extension path1 ^ ".hes" in
      Muapprox.Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:path2 phi1
    | _ -> failwith "format should be \"hes\" or \"in\""
  in
  print_endline @@ "Converted to " ^ path2

let command =
  Command.basic
    ~summary:"Convert between HES formats"
    Command.Let_syntax.(
      let%map_open
          from = flag "--from" (required string) ~doc:"source file's format"
      and filepath = anon ("filepath" %: string)
      and show_forall = flag "--show-forall" no_arg ~doc:"include forall binding when convert to HES"
      in
      (fun () -> main filepath from show_forall)
    )

let () = Command.run command
