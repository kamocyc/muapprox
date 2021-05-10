open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)


let main path1 coe partial_analysis =
  let coe1, coe2 =
    match String.split coe ~on:',' with
    | [coe1; coe2] ->
      int_of_string coe1, int_of_string coe2
    | _ -> failwith "illegal coe format"
    in
  let phi1 = Muapprox.parse path1 false in
  let phi1', _ = Muapprox.add_arguments phi1 coe1 coe2 partial_analysis in
  let path2 = map_file_path path1 (fun (a, b, c) -> (a, b ^ "_add_args", c)) in
  let phi1' = Muapprox.abbrev_variable_numbers_hes phi1' in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi1';
  print_endline @@ "saved to " ^ path2
  
  
let command =
  Command.basic
    ~summary:"Check whether two hes files have differences"
    Command.Let_syntax.(
      let%map_open
          path1 = anon ("path1" %: string)
      and coe = anon ("coe" %: string) 
      and partial_analysis = flag "--partial-analysis" no_arg ~doc:"Do partial analysis"
      in
      (fun () -> main path1 coe partial_analysis)
    )

let () = Command.run command
