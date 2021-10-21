open Core

type output_format = FProgram | FOcamlLike | FHors

let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext)

let read_file file = In_channel.(with_file file ~f:input_all)
let write_file file buf = Out_channel.write_all file ~data:buf

let main filepath output_style =
  let buf = 
    let buf = read_file filepath in
    "%PROGRAM\n" ^ buf ^ "\n\n" ^ "%TRANSITION\nqa a -> qa\n\n%PRIORITY\nqa -> 1" in
  let file =
    let r = Random.int 0x10000000 in
    Printf.sprintf "/tmp/%d.tmp" r in
  write_file file buf;
  print_endline @@ "file: " ^ file;
  let program, _ = Muapprox.ltl_parse_file file in
  let program = Muapprox.convert_all program in
  let path2 = map_file_path filepath (fun (a, b, c) -> (a, b ^ "_out", c)) in
  let buf =
    match output_style with
    | FProgram -> Muapprox.Ltl_print_syntax.show_program program
    | FOcamlLike -> Muapprox.Ltl_print_syntax.show_program_as_ocaml program
    | FHors -> Muapprox.Ltl_print_syntax.show_program_as_hors program
    in
  write_file path2 buf;
  print_endline @@ "Program: " ^ path2
  
let read_output_style = 
  Command.Arg_type.create (fun style ->
      match style with
      | "program" -> FProgram
      | "ocaml" -> FOcamlLike
      | "hors" -> FHors
      | _ -> failwith "style should be one of raw, escape, or abbrev")

let command =
  Command.basic
    ~summary:"Return a \"program\" of the given HES formula"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      and output_style = flag "--output-style" (optional_with_default FProgram read_output_style) ~doc:"output style"
      in
      (fun () -> main filepath output_style)
    )

let () = Command.run command
