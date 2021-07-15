let () =
  let file =
    match Muapprox.Options.parse() with
    | Some (`File file) -> file
    | Some `Stdin ->
        let tmp_file = Filename.temp_file "stdin-" ".in" in
        let contents = Hflmc2_util.In_channel.(input_all stdin) in
        Hflmc2_util.Out_channel.with_file tmp_file ~f:begin fun ch ->
          Hflmc2_util.Out_channel.output_string ch contents
        end;
        tmp_file
    | None -> exit 1
  in
    Muapprox.main file (fun (s, debug_contexts) -> 
      match s with
      | r ->
          if Logs.Src.level Muapprox.log_src <> None then begin
            Fmt.pr "@[<v 2>[[MAIN]] Verification Result:@,%s@]@." @@ Muapprox.show_result r;
            Muapprox.report_times ();
            print_endline @@ Muapprox.show_debug_contexts debug_contexts
          end else 
            Fmt.pr "%s\n" (Muapprox.show_result r);
      | exception
          ( Muapprox.Util.Fn.Fatal e
          | Muapprox.Syntax.ParseError e
          | Muapprox.Syntax.LexingError e
          ) -> print_endline e; exit 1
    )