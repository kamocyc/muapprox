open Core

let main path1 =
  let phi1 = Muapprox.parse path1 in
  Muapprox.Manipulate.Hflz_typecheck.ensure_no_shadowing phi1;
  print_endline "OK"

let command =
  Command.basic
    ~summary:"Infer flag test"
    Command.Let_syntax.(
      let%map_open
          path = anon ("path1" %: string)
      in
      (fun () -> main path)
    )

let () = Command.run command
