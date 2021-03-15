open Core

type show_style = Raw_id | Escape_id | Abbrev_id

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath =
  let hes = Muapprox.branching_time_program filepath in
  ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"aaa.txt" ~without_id:true true hes;
  let hes = Muapprox.eliminate_unused_argument hes in
  ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"bbb.txt" ~without_id:true true hes;
  let hes = Manipulate.Hes_optimizer.simplify hes in
  ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"ccc.txt" ~without_id:true true hes;
  ()
  
let command =
  Command.basic
    ~summary:"Convert program with LTL formula"
    Command.Let_syntax.(
      let%map_open filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath)
    )

let () = Command.run command
