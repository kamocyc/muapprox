open Core

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)


let main path1 coe eliminate_unused_arguments partial_analysis use_related =
  let coe1, coe2 =
    match String.split coe ~on:',' with
    | [coe1; coe2] ->
      int_of_string coe1, int_of_string coe2
    | _ -> failwith "illegal coe format"
    in
  let phi1 = Muapprox.parse path1 false in
  let phi1', id_type_map = Muapprox.add_arguments phi1 coe1 coe2 partial_analysis use_related in
  let phi1' =
    if eliminate_unused_arguments then
      Manipulate.Eliminate_unused_argument.eliminate_unused_argument ~id_type_map phi1'
    else phi1' in
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
      and eliminate_unused_arguments = flag "--eliminate-unused-arguments" no_arg ~doc:"Eliminate unused arguments"
      and use_related = flag "--use-related" no_arg ~doc:"Do related arguments analysis"
      in
      (fun () -> main path1 coe eliminate_unused_arguments partial_analysis use_related)
    )

let () = Command.run command
