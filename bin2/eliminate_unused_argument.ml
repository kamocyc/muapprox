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
  (* let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_elim_org", c)) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 true hes; *)
  (* let hes = Muapprox.infer_type hes in *)
  let hes = Muapprox.eliminate_unused_argument hes in
  let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_elim", c)) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true hes;
  (* ignore @@ Muapprox.Manipulate.Print_syntax.AsProgram.save_hes_to_file ~file:path2 hes; *)
  print_endline @@ "Program: " ^ path2
  
let command =
  Command.basic
    ~summary:"Eliminate unused arguments in HFLz"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath)
    )

let () = Command.run command
