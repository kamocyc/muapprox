open Core

type show_style = Raw_id | Escape_id | Abbrev_id

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath show_style disable_optimization solve always_use_canonical_type_env use_branching_time =
  let show_raw_id_name = match show_style with Raw_id -> true | _ -> false in
  let phi, _ = Muapprox.convert_ltl filepath show_raw_id_name always_use_canonical_type_env use_branching_time in
  let phi =
    if not disable_optimization then
      let phi = Manipulate.Hes_optimizer.simplify phi in
      let hflz = Muapprox.eliminate_unused_argument phi in
      Manipulate.Hes_optimizer.simplify hflz
    else phi in
  let phi =
    match show_style with
    | Abbrev_id -> Muapprox.abbrev_variable_names phi
    | _ -> phi in
  let path2 = map_file_path filepath (fun (a, b, _) -> (a, b, ".in")) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi;
  print_endline @@ "saved: " ^ path2;
  if solve then begin
    ignore @@ Unix.system @@ "dune exec ./bin/muapprox_main.exe -- --instantiate-exists \"" ^ path2 ^ "\""
  end
  
let read_show_style = 
  Command.Arg_type.create (fun style ->
      match style with
      | "raw" -> Raw_id
      | "escape" -> Escape_id
      | "abbrev" -> Abbrev_id
      | _ -> failwith "style should be one of raw, escape, or abbrev")

let command =
  Command.basic
    ~summary:"Convert program with LTL formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and show_style =
        flag "--show-style" (optional_with_default Abbrev_id read_show_style) ~doc:"output style of id (raw: output id in raw ascii format (only for debug), escape: escape id, abbrev: abbreviate id with serial number suffix (default)) "
      and disable_optimization = flag "--disable-optimization" no_arg ~doc:"disable elimination of unused arguments"
      and solve = flag "--solve" no_arg ~doc:"also solve the resulting hflz"
      and always_use_canonical_type_env = flag "--use-canonical-type" no_arg ~doc:"always use canonical intersection type environment even if input file contains environment"
      and use_branching_time = flag "--use-branching-time" no_arg ~doc:"convert program to HFLz using an algorithm for branching time properties"
      in
      (fun () -> main filepath show_style disable_optimization solve always_use_canonical_type_env use_branching_time)
    )

let () = Command.run command
