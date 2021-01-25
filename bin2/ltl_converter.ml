open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath =
  Muapprox.convert_ltl filepath
  
let command =
  Command.basic
    ~summary:"Convert program with LTL formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath)
    )

let () = Command.run command
