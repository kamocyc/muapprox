open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath =
  let hes = Muapprox.parse filepath in
  let hes = Muapprox.Manipulate.Hflz_manipulate.get_dual_hes hes in
  let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_dual", c)) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true hes;
  print_endline @@ "Dual: " ^ path2
  
let command =
  Command.basic
    ~summary:"Return the dual of the given HES formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath)
    )

let () = Command.run command
