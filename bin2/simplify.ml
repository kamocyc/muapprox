open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath is_hes =
  let hes = Muapprox.parse filepath is_hes in
  let hes = Muapprox.Manipulate.Hes_optimizer.simplify hes in
  let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_simplified", c)) in
  if is_hes then (
    ignore @@ Muapprox.Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:path2 hes
  ) else (
    ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 true hes);
  print_endline @@ "Simplified to " ^ path2
  
let command =
  Command.basic
    ~summary:"Simplify HES formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and is_hes = flag "--hes" no_arg ~doc:"Load hes format"
      in
      (fun () -> main filepath is_hes)
    )

let () = Command.run command
