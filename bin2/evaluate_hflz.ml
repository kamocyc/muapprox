open Core

(* let map_file_path path converter =
  let dir, base, ext =
    Stdlib.Filename.dirname path,
    Stdlib.Filename.remove_extension (Stdlib.Filename.basename path),
    Stdlib.Filename.extension path in
  let dir, base, ext = converter (dir, base, ext) in
  Stdlib.Filename.concat dir (base ^ ext) *)

let main path1 =
  let phi1 = Muapprox.parse path1 in
  let phi1 = Muapprox.Manipulate.Evaluate_hflz.evaluate_hes phi1 in
  ignore @@ phi1


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
