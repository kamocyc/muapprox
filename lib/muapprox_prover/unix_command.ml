open Async

(* This mutable data structure is accessed by multiple threads.
   However, this is safe because Async uses cooperative multithreading (not preemptive threads)
   therefore all operations, except ones have 'a Deferred.t type, are "atomic."
   (c.f. https://stackoverflow.com/questions/27784389/mutable-data-with-ocaml-and-jane-street-async) *)
let pids: (string, string list) Hashtbl.t = Hashtbl.create 2

let append_to_hashtbl_of_list tbl k e =
  match Hashtbl.find_opt tbl k with
  | None -> Hashtbl.add tbl k [e]
  | Some l -> Hashtbl.replace tbl k (e::l)

let kill_processes mode =
  match mode with
  | None -> Deferred.return ()
  | Some mode -> begin
    (* eld and java are not executed when ran with --no-disprove because they are used only to prove invalid *)
    (* TODO: main.exe should be renamed *)
    match Hashtbl.find_opt pids mode with
    | None -> Deferred.return ()
    | Some pid_filenames -> begin
      (* print_endline @@ "mode=" ^ mode ^ ", pid_filenames=" ^ (String.concat ", " pid_filenames);
      Hashtbl.remove pids mode; *)
      let comma_sep_pid_filenames = List.map String.trim pid_filenames |> (String.concat ",") in
      (* https://stackoverflow.com/a/3211182/12976091 *)
      (* https://stackoverflow.com/a/13481601/12976091 *)
      let killptree_command = {|
      killtree() {
        local _pid=$1
        local _sig=${2:-TERM}
        kill -stop ${_pid} # needed to stop quickly forking parent from producing child between child killing and parent killing
        for _child in $(ps -o pid --no-headers --ppid ${_pid}); do
            killtree ${_child} ${_sig}
        done
        kill -${_sig} ${_pid}
        kill -cont ${_pid}  # stopped processes are not SIGTERMed!!
        # wait ${_pid} 2>/dev/null || true  # for suppress "Terminated" message, but it takes time(?)
      }
      for pid in `echo |} ^ comma_sep_pid_filenames ^ {| | sed "s/,/ /g"`
      do
        killtree `cat $pid`
      done
      |} in
      let command = "bash -c '" ^ killptree_command ^ "' 2> /dev/null " in
      (* let process_names = ["hflmc2"; "main.exe"; "z3"; "hoice"] in
      let kill_command = String.concat "; " (List.map (fun n -> "pkill " ^ n) process_names) in *)
      (* save_string_to_file "/tmp/aaaaa.txt" command; *)
      (* print_endline @@ "kill command=" ^ command; *)
      (* failwith "a"; *)
      Unix.system command
    end >>| (fun _ -> Hashtbl.remove pids mode; ())
  end

let unix_system ?(no_quote=false) commands mode =
  (* quote *)
  (* 環境変数をセットするためにquoteしない *)
  let commands =
    if no_quote then Array.to_list commands
    else Array.to_list commands |> List.map (fun c -> "\"" ^ c ^ "\"") 
    in
  let r = Random.int 0x10000000 in
  let stdout_name = Printf.sprintf "/tmp/%d_stdout.tmp" r in
  let stderr_name = Printf.sprintf "/tmp/%d_stderr.tmp" r in
  let pid_name = Printf.sprintf "/tmp/%d_pid.tmp" r in
  let commands = commands @ [">"; stdout_name; "2>"; stderr_name] in
  print_endline @@ "run command (unix_system): " ^ (String.concat " " commands);
  let command = String.concat " " commands in
  let command = command ^ " &\nbpid=$!\necho $bpid > " ^ pid_name ^ "\nwait $bpid" in
  (match mode with
  | Some mode -> append_to_hashtbl_of_list pids mode pid_name
  | None -> ());
  let start_time = Stdlib.Sys.time () in
  Unix.system command 
  >>= (fun code ->
    let elapsed = Stdlib.Sys.time () -. start_time in
    Reader.file_contents stdout_name >>= (fun stdout ->
      Reader.file_contents stderr_name >>| (fun stderr ->
        code, elapsed, stdout, stderr
      )
    )
  )