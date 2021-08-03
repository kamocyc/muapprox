open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)


let main path1 old debug simplified_type new_f =
  let phi1 = Muapprox.parse path1 false in
  (* let path2 = map_file_path path1 (fun (a, b, c) -> (a, b ^ "_infer_flag", c)) in *)
  let phi1' =
    if new_f then begin
      (* Muapprox.Manipulate.Type_hflz5.output_debug_info := debug;
      Muapprox.Manipulate.Type_hflz5.infer phi1 *)
      Muapprox.Manipulate.Type_hflz7.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz7.infer phi1
    end else if old then begin
      Muapprox.Manipulate.Type_hflz2.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz2.infer phi1
    end else begin
      Muapprox.Manipulate.Type_hflz4.output_debug_info := debug;
      Muapprox.Manipulate.Type_hflz4.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz4.infer phi1
    end
  in
  ignore @@ phi1'
  (* ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi1'; *)
  (* print_endline @@ "saved to " ^ path2 *)


let command =
  Command.basic
    ~summary:"Infer flag test"
    Command.Let_syntax.(
      let%map_open
          path = anon ("path1" %: string)
      and old = flag "--old" no_arg ~doc:"Use old algorithm"
      and debug = flag "--debug" no_arg ~doc:"Output debug info"
      and new_f = flag "--new" no_arg ~doc:"Use new algorithm"
      and simplified_type = flag "--simplified-type" no_arg ~doc:"Show types as simplified format"
      in
      (fun () -> main path old debug simplified_type new_f)
    )

let () = Command.run command