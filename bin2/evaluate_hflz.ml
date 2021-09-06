open Core

(* let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext) *)

let main path1 =
  let phi1 = Muapprox.parse path1 false in
  let phi1 = Muapprox.Manipulate.Evaluate_hflz.evaluate_hes phi1 in
  ignore @@ phi1
  (* let path2 = map_file_path path1 (fun (a, b, c) -> (a, b ^ "_infer_flag_2", c)) in *)
  (* let phi1' =
    if new_f then begin
      (* Muapprox.Manipulate.Type_hflz5.output_debug_info := debug;
      Muapprox.Manipulate.Type_hflz5.infer phi1 *)
      Muapprox.Manipulate.Type_hflz7_def.output_debug_info := debug;
      Muapprox.Manipulate.Type_hflz7_def.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz7_pa_infer_partial_application.infer phi1
      (* failwith "OK"; *)
      (* Muapprox.Manipulate.Type_hflz7.infer phi1 *)
    end else if old then begin
      Muapprox.Manipulate.Type_hflz2.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz2.infer phi1
    end else begin
      Muapprox.Manipulate.Type_hflz4.output_debug_info := debug;
      Muapprox.Manipulate.Type_hflz4.simplified_type := simplified_type;
      Muapprox.Manipulate.Type_hflz4.infer phi1
    end
  in
  (* ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:false true phi1'; *)
  let phi1' = Muapprox.abbrev_variable_numbers_hes phi1' in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi1' *)
  (* print_endline @@ "saved to " ^ path2 *)


let command =
  Command.basic
    ~summary:"Evaluate HFLz"
    Command.Let_syntax.(
      let%map_open
          path = anon ("path1" %: string)
      in
      (fun () -> main path)
    )

let () = Command.run command
