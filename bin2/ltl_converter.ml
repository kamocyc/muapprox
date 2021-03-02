open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath show_raw_id_name always_use_canonical_type_env =
  let phi, _ = Muapprox.convert_ltl filepath show_raw_id_name always_use_canonical_type_env in
  let path2 = map_file_path filepath (fun (a, b, _) -> (a, b, ".in")) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi;
  print_endline @@ "saved: " ^ path2
  
let command =
  Command.basic
    ~summary:"Convert program with LTL formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and show_raw_id_name = flag "--raw-id" no_arg ~doc:"output id without escaping (for debug)"
      and always_use_canonical_type_env = flag "--use-canonical-type" no_arg ~doc:"always use canonical intersection type environment even if input file contains environment"
      in
      (fun () -> main filepath show_raw_id_name always_use_canonical_type_env)
    )

let () = Command.run command
