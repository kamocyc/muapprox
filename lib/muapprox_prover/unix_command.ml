type process_status = Unix.process_status
module Unix_old = Unix

open Async

let log_src = Logs.Src.create "Unix_command"
module Log = (val Logs.src_log @@ log_src)

let log_string = Manipulate.Hflz_util.log_string Log.info
let warn_string = Manipulate.Hflz_util.log_string Log.warn

(* This mutable data structure is accessed by multiple threads.
   However, this is safe because Async uses cooperative multithreading (not preemptive threads)
   therefore all operations, except ones have 'a Deferred.t type, are "atomic."
   (c.f. https://stackoverflow.com/questions/27784389/mutable-data-with-ocaml-and-jane-street-async) *)
let pids: (string, string list) Hashtbl.t = Hashtbl.create 2

let append_to_hashtbl_of_list tbl k e =
  match Hashtbl.find_opt tbl k with
  | None -> Hashtbl.add tbl k [e]
  | Some l -> Hashtbl.replace tbl k (e::l)

let pp_process_result fmt stat =
  let show_process_status : process_status -> string = function
    | WEXITED code -> "WEXITED(" ^ (string_of_int code) ^ ")"
    | WSIGNALED code -> "WSIGNALED(" ^ (string_of_int code) ^ ")"
    | WSTOPPED code -> "WSTOPPED(" ^ (string_of_int code) ^ ")" in
  Format.pp_print_string fmt @@ "Process result:\n";
  (* Format.pp_print_string fmt @@ "out: " ^ out ^ "\n"; *)
  Format.pp_print_string fmt @@ "status: " ^ (show_process_status stat) ^ "\n"

let show_code (code : (unit, [ `Exit_non_zero of int | `Signal of Hflmc2_util.Core.Signal.t ]) result) =
  match code with
  | Ok () -> "Ok"
  | Error code -> begin
    match code with
    | `Exit_non_zero code ->
      "`Exit_non_zero (" ^ string_of_int code ^ ")"
    | `Signal signal -> begin
      "`Signal (" ^ Signal.to_string signal ^ ")"
    end
  end

let kill_processes mode =
  match mode with
  | None -> Deferred.return ()
  | Some mode -> begin
    (* eld and java are not executed when ran with --no-disprove because they are used only to prove invalid *)
    match Hashtbl.find_opt pids mode with
    | None -> Deferred.return ()
    | Some pid_filenames -> begin
      Hashtbl.remove pids mode;
      let comma_sep_pid_filenames = List.map String.trim pid_filenames |> (String.concat ",") in
      let command = {|
      for pid in `echo |} ^ comma_sep_pid_filenames ^ {| | sed "s/,/ /g"`
      do
        kill -`cat $pid` 2> /dev/null
      done
      |} in
      Unix.system @@ command
      >>| (fun code ->
        match code with
        | Ok () -> begin
          ()
        end
        | Error code -> begin
          log_string @@ "Error status (kill_processes, " ^ show_code (Error code) ^ ")"
      end
      )
    end
  end

let () =
  Signal.handle Signal.terminating ~f:(fun signal ->
    let pid_filenames = Hashtbl.fold (fun _ v acc -> List.concat [v; acc]) pids [] in
    
    let comma_sep_pid_filenames = List.map String.trim pid_filenames |> (String.concat ",") in
    let command = {|
    for pid in `echo |} ^ comma_sep_pid_filenames ^ {| | sed "s/,/ /g"`
    do
      echo KILL2: "-|} ^ Signal.to_string signal ^ {| `cat $pid`"
      bash -c "kill -|} ^ Signal.to_string signal ^ {| `cat $pid`" # 2> /dev/null
    done
    |} in
    let code = Unix_old.system command in
    (match code with
    | WEXITED 0 -> ()
    | _ -> begin
      warn_string "Error when killing processes";
      pp_process_result Format.std_formatter code
    end);
    ignore @@ Signal.default_sys_behavior signal;
    shutdown 0
  )
  
let unix_system ?env timeout commands mode =
  let open Core in
  let module Proc = Async_unix.Process in
  let command, arguments =
    let commands =
      if true then Array.to_list commands
      else Array.to_list commands |> List.map ~f:(fun c -> "\"" ^ c ^ "\"") 
      in
    "timeout", [string_of_int timeout] @ commands in
  
  log_string @@ "Run command: " ^ command ^ " " ^ (String.concat ~sep:" " arguments);
  
  let r = Random.int 0x10000000 in
  let pid_name = Printf.sprintf "/tmp/%d_pid.tmp" r in
  (match mode with
  | Some mode -> append_to_hashtbl_of_list pids mode pid_name
  | None -> ());
  
  let start_time = Stdlib.Sys.time () in
  
  let env =
    match env with
    | None -> []
    | Some e -> e in
    
  Proc.create ~prog:command ~args:arguments ~env:(`Extend env) ()
  >>= (fun process_opt ->
    match process_opt with
    | Ok process -> begin
      let pid = Proc.pid process in
      let pid_i = Pid.to_int pid in
      Writer.save pid_name ~contents:(string_of_int pid_i ^ "\n")
      >>= (fun () ->
        Proc.collect_output_and_wait process
        >>| (fun output ->
          let elapsed = Stdlib.Sys.time () -. start_time in
          let {Proc.Output.stdout; stderr; exit_status} = output in
          exit_status, elapsed, stdout, stderr
        )
      )
    end
    | Error result -> begin
      failwith @@ "Command error (1): " ^ Error.to_string_hum result 
    end
  )
