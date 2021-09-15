open Core

type show_style = Asis_id | Abbrev_id

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let main filepath is_hes optimization agg show_style =
  let hes = Muapprox.parse filepath is_hes in
  let hes =
    if optimization then Muapprox.eliminate_unused_argument hes else hes in
  let hes = Muapprox.Manipulate.Hes_optimizer.simplify_all hes in
  let hes =
    if agg then Manipulate.Hes_optimizer.simplify_agg hes else hes in
  let hes =
    match show_style with
    | Abbrev_id -> Muapprox.abbrev_variable_names hes
    | Asis_id -> hes in
  let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_simplified", c)) in
  if is_hes then (
    ignore @@ Muapprox.Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:path2 hes
  ) else (
    ignore @@ Muapprox.Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path2 ~without_id:(Stdlib.(=) show_style Abbrev_id) true hes);
  print_endline @@ "Simplified to " ^ path2

let read_show_style = 
  Command.Arg_type.create (fun style ->
      match style with
      | "asis" -> Asis_id
      | "abbrev" -> Abbrev_id
      | _ -> failwith "style should be one of raw, escape, or abbrev")
  
let command =
  Command.basic
    ~summary:"Simplify HES formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and is_hes = flag "--hes" no_arg ~doc:"Load hes format"
      and optimization = flag "--optimization" no_arg ~doc:"eliminatate unused arguments"
      and agg = flag "--agg" no_arg ~doc:"aggressive inlining"
      and show_style =
        flag "--show-style" (optional_with_default Asis_id read_show_style) ~doc:"output id without escaping (for debug)"
      in
      (fun () -> main filepath is_hes optimization agg show_style)
    )

let () = Command.run command
