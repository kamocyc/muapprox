open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath =
  let phi1 = Muapprox.parse filepath false in
  let phi = Muapprox.branching_time_program is_horsz filepath in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi;
  print_endline @@ "saved: " ^ path2
  
let command =
  Command.basic
    ~summary:""
    Command.Let_syntax.(
      let%map_open
        filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath )
    )

let () = Command.run command
