open Core

let main path1 show_forall =
  let phi1 = Muapprox.parse path1 in
  let path2 = Stdlib.Filename.remove_extension path1 ^ ".in" in
  let path2 = Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 show_forall phi1 in
  print_endline @@ "Converted to " ^ path2

let command =
  Command.basic
    ~summary:"Convert between HES formats"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and show_forall = flag "--show-forall" no_arg ~doc:"include forall binding when convert to HES"
      in
      (fun () -> main filepath show_forall)
    )

let () = Command.run command
