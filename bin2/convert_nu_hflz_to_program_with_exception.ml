open Core

let main path1 =
  let phi1 = Muapprox.parse path1 in
  let output =
    Hflmc2_util.fmt_string Muapprox.convert_nu_hflz_to_program_with_exception phi1 in
  print_endline output

let command =
  Command.basic
    ~summary:"Convert between HES formats"
    Command.Let_syntax.(
      let%map_open
          filepath = anon ("filepath" %: string)
      in
      (fun () -> main filepath)
    )

let () = Command.run command
