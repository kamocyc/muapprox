open Core

type show_style = Asis_id | Abbrev_id

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath disable_optimization show_style =
  let phi = Muapprox.branching_time_program filepath in
  let phi =
    if not disable_optimization then
      let phi = Muapprox.eliminate_unused_argument phi in
      Manipulate.Hes_optimizer.simplify phi
    else phi in
  let phi =
    match show_style with
    | Abbrev_id -> Muapprox.abbrev_variable_names phi
    | Asis_id -> phi in
  let path2 = map_file_path filepath (fun (a, b, _) -> (a, b, ".in")) in
  ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:true true phi;
  print_endline @@ "saved: " ^ path2
  
let read_show_style = 
  Command.Arg_type.create (fun style ->
      match style with
      | "asis" -> Asis_id
      | "abbrev" -> Abbrev_id
      | _ -> failwith "style should be one of raw, escape, or abbrev")
      
let command =
  Command.basic
    ~summary:"Convert program with Alternating tree automaton"
    Command.Let_syntax.(
      let%map_open
        filepath = anon ("filepath" %: string)
      and disable_optimization = flag "--disable-optimization" no_arg ~doc:"disable elimination of unused arguments"
      and show_style =
        flag "--show-style" (optional_with_default Asis_id read_show_style) ~doc:"output id without escaping (for debug)"
      in
      (fun () -> main filepath disable_optimization show_style)
    )

let () = Command.run command
