module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status
module Solve_options = Solve_options
module Hflz_mani = Manipulate.Hflz_manipulate
module Check_formula_equality = Check_formula_equality
module Abbrev_variable_numbers = Abbrev_variable_numbers
module Mochi_solver = Mochi_solver

open Async
open Solve_options
open Unix_command

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

let log_string = Manipulate.Hflz_util.log_string Log.info
let message_string = Manipulate.Hflz_util.log_string Log.app

type debug_context = {
  coe1: int;
  coe2: int;
  add_arg_coe1: int;
  add_arg_coe2: int;
  iter_count: int;
  mode: string;
  pid: int;
  file: string;
  temp_file: string;
  backend_solver: string option;
  default_lexicographic_order: int;
  exists_assignment: (unit Hflmc2_syntax.Id.t * int) list option;
  t_count: int;
  s_count: int;
  elapsed_all: float;
  will_try_weak_subtype: bool;
}

let has_solved = ref false

let show_debug_context debug =
  let show assoc =
    let rec go = function 
      | [] -> []
      | (k, v)::xs -> (k ^ ": " ^ v)::(go xs) in
    "(" ^ (go assoc |> String.concat ", ") ^ ")"
  in
  let soi = string_of_int in
  let unwrap_or alt opt = match opt with None -> alt | Some s -> s in
  debug.mode ^ "-" ^ soi debug.iter_count ^ " (" ^ (Option.value debug.backend_solver ~default:"-") ^ "): " ^
  show [
    ("coe1", soi debug.coe1);
    ("coe2", soi debug.coe2);
    ("add_arg_coe1", if debug.add_arg_coe1 = 0 then "-" else soi debug.add_arg_coe1);
    ("add_arg_coe2", if debug.add_arg_coe1 = 0 then "-" else soi debug.add_arg_coe2);
    ("default_lexicographic_order", string_of_int debug.default_lexicographic_order);
    ("exists_assignment", Option.map (fun m -> "[" ^ ((List.map (fun (id, v) -> id.Hflmc2_syntax.Id.name ^ "=" ^ string_of_int v) m) |> String.concat "; ") ^ "]") debug.exists_assignment |> unwrap_or "-");
    ("t_count", soi debug.t_count);
    ("s_count", soi debug.s_count);
    ("elapsed_all", string_of_float debug.elapsed_all);
    ("temp_file", debug.temp_file);
    ("will_try_weak_subtype", string_of_bool debug.will_try_weak_subtype)
  ]

let show_debug_contexts debugs =
  List.map
    (fun debug ->
      show_debug_context debug
    )
    debugs |>
  String.concat ", "
  
module type BackendSolver = sig
  val run : options -> debug_context -> Hflmc2_syntax.Type.simple_ty Hflz.hes -> bool -> bool -> bool -> Status.t Deferred.t
end

module FptProverRecLimitSolver : BackendSolver = struct
  let get_first_order_solver_path () =
    match Stdlib.Sys.getenv_opt "first_order_solver_path" with
    | None -> failwith "Please set environment variable `first_order_solver_path`"
    | Some s -> s
  
  let run option _debug_context (hes : 'a Hflz.hes) with_par _ _ =
    let solver_path = get_first_order_solver_path () in
    let debug_output =
      match option.log_level with
      | Some Info | Some Debug -> true
      | _ -> false in
    let path = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes in
    let command =
      [solver_path; path; "--timeout"; string_of_int option.timeout]
      @ (if with_par then ["--paralell"] else [])
      @ (if debug_output then ["--debug-output"] else [])
      in
    Unix_command.unix_system (option.timeout + 5) (Array.of_list command) None
    >>| (fun (code, _elapsed, stdout, _stderr) ->
      match code with
      | Ok () -> begin
        if debug_output then print_endline stdout;
        let reg = Str.regexp "^Verification Result: \\([a-z]+\\)$" in
        try
          ignore @@ Str.search_forward reg stdout 0;
          Status.of_string @@ Str.matched_group 1 stdout
        with
        | Not_found ->
          log_string "Failure in parsing output";
          Status.Fail
      end
      | Error code -> begin
        log_string @@ "Error status (" ^ Unix_command.show_code (Error code) ^ ")";
        Status.Fail
      end
    )
end

let output_json data file_path =
  let oc = Stdio.Out_channel.create ~append:true (file_path) in
  Yojson.Basic.pretty_to_channel oc data;
  Stdio.Out_channel.close oc

let get_file_name prefix file mode iter_count =
  prefix ^ "_" ^ Filename.remove_extension (Filename.basename file) ^ "_" ^ mode ^ "_" ^ string_of_int iter_count ^ ".tmp"

let output_post_merged_debug_info (dbg : debug_context) =
  let data = 
    `Assoc ([
      ("mode", `String dbg.mode);
      ("pid", `Int dbg.pid);
      ("file", `String dbg.file);
      
      ("iter_count", `Int dbg.iter_count);
      ("t_count", `Int dbg.t_count);
      ("s_count", `Int dbg.s_count);
      ("elapsed_all", `Float dbg.elapsed_all)]) in
  output_json data (get_file_name "post_merged" dbg.file dbg.mode dbg.iter_count)
  
module SolverCommon = struct

  type temp_result_type =
    | TValid
    | TInvalid
    | TUnknown
    | TTerminated
    | TFail
    | TError
  
  let to_string_result = function
    | TValid -> "valid"
    | TInvalid -> "invalid"
    | TUnknown -> "unknown"
    | TTerminated -> "terminated"
    | TFail -> "fail"
    | TError -> "error"
  
  let output_pre_debug_info_sub (dbg : debug_context) path =
    let data =
      `Assoc ([
        ("mode", `String dbg.mode);
        ("pid", `Int dbg.pid);
        ("path", `String path);
        ("file", `String dbg.file);
        ("backend_solver", `String (Option.value dbg.backend_solver ~default:""));
        
        ("iter_count", `Int dbg.iter_count);
        ("coe1", `Int dbg.coe1);
        ("coe2", `Int dbg.coe2);
        ("t_count", `Int dbg.t_count);
        ("s_count", `Int dbg.s_count);
      ]) in
    output_json data (get_file_name "pre" dbg.file dbg.mode 0)
    
  let output_pre_debug_info hes debug_context path no_temp_files =
    let path' = 
      let hes = Abbrev_variable_numbers.abbrev_variable_numbers_hes hes in
      let file = Filename.basename debug_context.file ^ "__" ^ debug_context.mode ^ "__" ^ string_of_int debug_context.iter_count ^ ".in" in
      if not no_temp_files then
        Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:file ~without_id:true true hes
      else file in
    message_string ~header:"SolveInfo" @@ "νHFLz, " ^ (show_debug_context {debug_context with temp_file = path}) ^ ": " ^ path';
    if not no_temp_files then output_pre_debug_info_sub debug_context path';
    ()
    
  let output_post_debug_info tmp_res elapsed stdout stderr debug_context =
    let data = 
      `Assoc ([
        ("result", `String (to_string_result tmp_res));
        ("time", `Float elapsed);
        ("stdout", `String stdout);
        ("stderr", `String stderr);
        
        ("iter_count", `Int debug_context.iter_count);
        ("mode", `String debug_context.mode);
        ("backend_solver", `String (Option.value debug_context.backend_solver ~default:""));
        ("file", `String debug_context.file);
        ("coe1", `Int debug_context.coe1);
        ("coe2", `Int debug_context.coe2);
        ("pid", `Int debug_context.pid);
        ("will_try_weak_subtype", `Bool debug_context.will_try_weak_subtype);
      ]) in
    output_json data (get_file_name "post" debug_context.file debug_context.mode 0)
  
  type solver_error_category = S_ParseError | S_TypeError | S_OtherError
  
  let parse_results_inner (exit_status, stdout, stderr) debug_context elapsed no_temp_files status_parser =
    let res, tmp_res, log_message, stopped_when_intractable = 
      match exit_status with 
      | Ok () -> begin
        let status, stopped_when_intractable = status_parser stdout in
        status, (
        match status with
        | Status.Valid -> TValid
        | Invalid -> TInvalid
        | _ -> TUnknown),
        "Parsed status: " ^ Status.string_of status ^ " " ^ (show_debug_context debug_context), stopped_when_intractable
      end
      | Error (`Exit_non_zero 2) -> begin
        Status.Fail, TTerminated,
        "Error code 2 " ^ (show_debug_context debug_context), false
      end
      | Error (`Exit_non_zero 127) -> begin
        Status.Fail, TTerminated,
        "Command not found " ^ (show_debug_context debug_context), false
      end
      | Error (`Exit_non_zero 143) -> begin
        Status.Unknown, TTerminated,
        "SIGTERMed " ^ (show_debug_context debug_context), false
      end
      | Error (`Exit_non_zero 128) -> begin
        (* SIGTERMed. (why 128?) *)
        Status.Unknown, TTerminated,
        "SIGTERMed (128) " ^ (show_debug_context debug_context), false
      end
      | Error (`Exit_non_zero 124) -> begin
        Status.Unknown, TUnknown,
        "Timeout " ^ (show_debug_context debug_context), false
      end
      | Error code -> begin
        Status.Unknown, TError,
        "Error status (" ^ Unix_command.show_code (Error code) ^ ")", false
      end
    in
    if not no_temp_files then output_post_debug_info tmp_res elapsed stdout stderr debug_context;
    if not stopped_when_intractable then
      message_string ~header:"Result" @@ Status.string_of res ^ " / " ^ log_message;
    res
  
  let run_command_with_timeout ?env timeout command mode =
    unix_system ?env timeout command mode
    
end

module MochiSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "mochi_path" with
    | None -> failwith "Please set environment variable `mochi_path`"
    | Some s -> s
    
  let save_hes_to_file hes mode debug_context no_temp_files =
    let buf =
      Hflmc2_util.fmt_string Mochi_solver.convert_nu_hflz_to_program_with_exception hes in
    let r = Random.int 0x10000000 in
    Sys.getcwd ()
    >>| (fun cwd ->
      (* MoCHi cannot operate on a file in /tmp directory *)
      cwd ^ "/mochi__temp__" ^ mode ^ "__" ^ string_of_int r ^ ".ml")
    >>= (fun file ->
      Writer.save file ~contents:buf
      >>| (fun () ->
        output_pre_debug_info hes debug_context file no_temp_files;
        file
      )
    )
  
  let solver_command path _solve_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path :: [path]
    )
  
  let parse_results result debug_context elapsed no_temp_files =
    parse_results_inner result debug_context elapsed no_temp_files (fun stdout ->
      let reg = Str.regexp "^\\(Safe!\\|Unsafe!\\)$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        match Str.matched_group 1 stdout with
        | "Safe!" -> Valid, false
        | "Unsafe!" -> Invalid, false
        | _ -> assert false
      with
      | Not_found ->
        Status.Fail, false
    )
    
  let run solve_options (debug_context: debug_context) hes _ _ _ = 
    save_hes_to_file hes debug_context.mode debug_context solve_options.no_temp_files
    >>= (fun path ->
      let debug_context = { debug_context with temp_file = path } in
      let command = solver_command path solve_options in
      run_command_with_timeout solve_options.timeout command (Some debug_context.mode) >>|
        (fun (status_code, elapsed, stdout, stderr) ->
          parse_results (status_code, stdout, stderr) debug_context elapsed solve_options.no_temp_files
        )
    )
end

let get_katsura_solver_path () =
  match Stdlib.Sys.getenv_opt "katsura_solver_path" with
  | None -> failwith "Please set environment variable `katsura_solver_path`"
  | Some s -> s
  
module KatsuraSolver : BackendSolver = struct
  include SolverCommon
  
  let replacer_path () =
    (Lazy.force Hflmc2_util.project_root_directory) ^ "/benchmark/replacer.py"
    
  let is_valid_replacer_name replacer =
    let command = "python3 " ^ replacer_path () ^ " " ^ replacer ^ " __dummy --check-target-name-only > /dev/null" in
    Unix.system command >>| (fun code ->
      match code with
      | Ok () -> true
      | Error (`Exit_non_zero 3) -> false
      | Error (`Exit_non_zero 2) -> failwith @@ replacer_path () ^ " not found (python3 returned exit code 2)"
      | Error _ -> failwith "is_valid_replacer_name: illegal result"
    )
    
  let save_hes_to_file hes replacer debug_context with_usage_analysis with_partial_analysis no_temp_files =
    let should_use_replacer =
      if replacer <> "" then
        is_valid_replacer_name replacer
        >>| (fun res ->
          if not res then message_string @@ "[Warning] replacer \"" ^ replacer ^ "\" is specified, but not used because it is invalid name";
          res
        )
      else Deferred.return false in
    should_use_replacer
    >>= (fun should_use_replacer ->
      let path =
        if should_use_replacer then begin
          log_string "using replacer";
          let hes = Abbrev_variable_numbers.abbrev_variable_numbers_hes hes in
          let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:true true hes in
          let r = Random.int 0x10000000 in
          let stdout_name = Printf.sprintf "/tmp/%d_stdout.tmp" r in
          let flag =
            if with_partial_analysis then (
              if with_usage_analysis then
                "noflags"
              else
                "nousage"
            ) else (
              if with_usage_analysis then
                "nopartial"
              else
                "noboth"
            ) in
          let command = "python3 " ^ replacer_path () ^ " --mode=" ^ flag ^ " " ^ replacer ^ " " ^ path ^ " > " ^ stdout_name in
          log_string @@ "command: " ^ command;
          Unix.system command
          >>= (fun code ->
            Reader.file_contents stdout_name >>| (fun stdout ->
              match code with
              | Ok () ->
                let stdout = String.trim stdout in
                log_string @@ "REPLACED!!: " ^ stdout;
                output_pre_debug_info hes debug_context stdout no_temp_files;
                stdout
              | Error _ -> failwith @@ "replacer error (filepath: " ^ path ^ " ): " ^ stdout
            )
          )
        end else
          let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false true hes in
          output_pre_debug_info hes debug_context path no_temp_files;
          Deferred.return path in
      path
    )
    
  let solver_command hes_path solver_options stop_if_intractable will_try_weak_subtype =
    let solver_path = get_katsura_solver_path () in
    Array.of_list (
      solver_path :: ["--solve-dual=auto-conservative"] @
        (if solver_options.no_disprove then ["--no-disprove"] else []) @
        (List.filter_map (fun x -> x)
          [
            (if solver_options.no_backend_inlining then Some "--no-inlining" else None);
            (match solver_options.backend_solver with None -> None | Some s -> Some ("--solver=" ^ s));
            (if stop_if_intractable then Some "--stop-if-intractable" else None);
            (if will_try_weak_subtype then Some "--mode-burn-et-al" else None);
            (if solver_options.backend_options <> "" then Some solver_options.backend_options else None)
          ]
        ) @
        [hes_path]
    )

  let parse_results result debug_context elapsed no_temp_files =
    parse_results_inner result debug_context elapsed no_temp_files (fun stdout ->
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nProfiling:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        Status.of_string @@ Str.matched_group 2 stdout, false
      with
      | Not_found -> begin
        let reg = Str.regexp "^intractable$" in
        try
          ignore @@ Str.search_forward reg stdout 0;
          message_string ~header:"Result" @@ "stop becasuse intractable (" ^ (show_debug_context debug_context) ^ ")";
          Status.Fail, true
        with
        | Not_found -> failwith @@ "not matched"
      end
    )
    
  let run solve_options (debug_context: debug_context) hes _ stop_if_intractable will_try_weak_subtype = 
    save_hes_to_file hes (if debug_context.mode = "prover" && solve_options.approx_parameter.add_arg_coe1 <> 0 && solve_options.approx_parameter.lexico_pair_number = 1 then solve_options.replacer else "") debug_context solve_options.with_usage_analysis solve_options.with_partial_analysis solve_options.no_temp_files
    >>= (fun path ->
      let debug_context = { debug_context with temp_file = path } in
      let command = solver_command path solve_options stop_if_intractable will_try_weak_subtype in
      if solve_options.dry_run then failwith @@ "DRY RUN (" ^ show_debug_context debug_context ^ ") / command: " ^ (Array.to_list command |> String.concat " ");
      run_command_with_timeout solve_options.timeout command (Some debug_context.mode) >>|
        (fun (status_code, elapsed, stdout, stderr) ->
          let r =
            match status_code with
            | Error (`Exit_non_zero 1) | Error (`Exit_non_zero 2) ->
              print_endline stdout;
              let lines = String.split_on_char '\n' (String.trim stdout) in
              if List.length lines >= 3 then begin
                let s = List.nth lines 1 in
                let tl = List.rev lines |> List.hd in
                print_endline @@ "tl: " ^ tl;
                if String.length s > 15 && String.sub s 0 14 = "Parse Error at" then
                  S_ParseError
                else if tl = "ill-typed" then S_TypeError
                else S_OtherError
              end else S_OtherError
            | _ -> S_OtherError
            in
          match r with
          | S_ParseError -> failwith @@ "Parse Error (" ^ show_debug_context debug_context ^ ")"
          | S_TypeError -> failwith @@ "Type Error (" ^ show_debug_context debug_context ^ ")"
          | _ ->
            try
              parse_results (status_code, stdout, stderr) debug_context elapsed solve_options.no_temp_files
            with _ -> Status.Unknown)
    )
end

module IwayamaSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "iwayama_solver_path" with
    | None -> failwith "Please set environment variable `iwayama_solver_path`"
    | Some s -> s
  
  let save_hes_to_file hes debug_context no_temp_files =
    let hes = Manipulate.Hflz_manipulate.encode_body_forall_except_top hes in
    let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false false hes in
    output_pre_debug_info hes debug_context path no_temp_files;
    path
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path::
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None]) @
        [hes_path]
    )

  let parse_results result debug_context elapsed no_temp_files =
    parse_results_inner result debug_context elapsed no_temp_files (fun stdout -> 
      (* Verification Result: の行を探す。 *)
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nLoop Count:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        Status.of_string @@ Str.matched_group 2 stdout, false
      with
        | Not_found -> failwith @@ "not matched"
    )
  
  let run solve_options debug_context hes _ _ _ = 
    let path = save_hes_to_file hes debug_context solve_options.no_temp_files in
    let debug_context = { debug_context with temp_file = path } in
    let command = solver_command path solve_options in
    run_command_with_timeout solve_options.timeout command (Some debug_context.mode)
    >>| (fun (status_code, elapsed, stdout, stderr) ->
        try
          parse_results (status_code, stdout, stderr) debug_context elapsed solve_options.no_temp_files
          with _ -> Status.Unknown)
end

module SuzukiSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "suzuki_solver_path" with
    | None -> failwith "Please set environment variable `suzuki_solver_path`"
    | Some s -> s
  
  let save_hes_to_file hes debug_context no_temp_files =
    Hflmc2_syntax.Print.global_not_output_zero_minus_as_negative_value := true;
    let hes = Manipulate.Hflz_manipulate.encode_body_forall_except_top hes in
    let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false false hes in
    output_pre_debug_info hes debug_context path no_temp_files;
    path
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path::
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None]) @
        [hes_path]
    )

  let parse_results result debug_context elapsed no_temp_files =
    parse_results_inner result debug_context elapsed no_temp_files (fun stdout -> 
      let reg = Str.regexp "^\\(Sat\\|UnSat\\)$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        let s = Str.matched_group 1 stdout in
        (* 出力"Sat"がvalidに対応する(？) *)
        Status.of_string (
          match s with
          | "Sat" -> "valid"
          | "UnSat" -> "invalid"
          | _ -> failwith @@ "Illegal status string1 (" ^ s ^ ")"
        ), false
      with
        | Not_found -> failwith @@ "not matched"
    )
  
  let run solve_options debug_context hes _ _ _ = 
    let path = save_hes_to_file hes debug_context solve_options.no_temp_files in
    let debug_context = { debug_context with temp_file = path }  in
    let command = solver_command path solve_options in
    run_command_with_timeout ~env:["RUST_LOG", " "] solve_options.timeout command (Some debug_context.mode)
    >>| (fun (status_code, elapsed, stdout, stderr) ->
        try
          parse_results (status_code, stdout, stderr) debug_context elapsed solve_options.no_temp_files
          with _ -> Status.Unknown)
end

let rec is_first_order_function_type (ty : Hflmc2_syntax.Type.simple_ty) =
  match ty with
  | TyBool () -> true
  | TyArrow (ty1, ty2) -> 
    ty1.ty = TyInt && is_first_order_function_type ty2
  
let is_first_order_hes hes =
  Hflz_mani.decompose_lambdas_hes hes
  |> (fun hes -> Hflz.merge_entry_rule hes)
  |> List.for_all (fun { Hflz.var; _} -> is_first_order_function_type var.ty)
  
let solve_onlynu_onlyforall solve_options debug_context hes with_par stop_if_intractable will_try_weak_subtype =
  let run =
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      FptProverRecLimitSolver.run
    ) else (
      match solve_options.solver with
      | Katsura -> KatsuraSolver.run
      | Iwayama -> IwayamaSolver.run
      | Suzuki  -> SuzukiSolver.run
      | Mochi -> MochiSolver.run
    ) in
  run solve_options debug_context hes with_par stop_if_intractable will_try_weak_subtype >>| (fun s -> (s, debug_context))
  
let fold_hflz folder phi init =
  let rec go phi acc = match phi with
    | Hflz.Bool   _ -> folder acc phi 
    | Hflz.Var    _ -> folder acc phi
    | Hflz.Or (f1, f2)  -> folder acc phi |> go f1 |> go f2
    | Hflz.And (f1, f2) -> folder acc phi |> go f1 |> go f2
    | Hflz.Abs (_, f1)  -> folder acc phi |> go f1
    | Hflz.Forall (_, f1) -> folder acc phi |> go f1
    | Hflz.Exists (_, f1) -> folder acc phi |> go f1
    | Hflz.App (f1, f2)   -> folder acc phi |> go f1 |> go f2
    | Hflz.Arith _ -> folder acc phi
    | Hflz.Pred _ -> folder acc phi in
  go phi init

let is_onlyforall_body formula =
  fold_hflz (fun b f -> match f with Hflz.Exists _ -> false | _ -> b) formula true
let is_onlynu_onlyforall_rule {Hflz.fix; body; _} =
  (fix = Fixpoint.Greatest) && is_onlyforall_body body
let is_onlynu_onlyforall (entry, rules) =
  is_onlyforall_body entry
  && (List.for_all is_onlynu_onlyforall_rule rules)

let is_onlyexists_body formula =
  fold_hflz (fun b f -> match f with Hflz.Forall _ -> false | _ -> b) formula true
let is_onlymu_onlyexists_rule {Hflz.fix; body; _} =
  (fix = Fixpoint.Least) && is_onlyexists_body body
let is_onlymu_onlyexists (entry, rules) =
  is_onlyexists_body entry
  && (List.for_all is_onlymu_onlyexists_rule rules)


let is_nu_only_tractable hes =
  let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false true hes in
  let solver_path = get_katsura_solver_path () in
  let r = Random.int 0x10000000 in
  let stdout_name = Printf.sprintf "/tmp/%d_stdout.tmp" r in
  let command = "\"" ^ solver_path ^ "\" --tractable-check-only \"" ^ path ^ "\" > " ^ stdout_name in
  log_string @@ "command: " ^ command;
  Unix.system command
  >>= (fun _ ->
    Reader.file_lines stdout_name >>| (fun stdout_lines ->
      match (List.rev stdout_lines) with
      | last_line::_ -> begin
        match last_line with
        | "tractable" -> true
        | "intractable" -> false
        | _ -> failwith @@ "run_tractable_check: Illegal result (" ^ last_line ^ ")"
      end
      | _ -> failwith @@ "run_tractable_check: No result"
    )
  )

let count_exists (entry, rules) =
  let rec go phi = match phi with
    | Hflz.Exists (_, p) -> 1 + go p
    | Var _ | Arith _ | Pred _ | Bool _ -> 0
    | Forall (_, p) -> go p
    | App (p1, p2) -> go p1 + go p2
    | And (p1, p2) -> go p1 + go p2
    | Or (p1, p2) -> go p1 + go p2
    | Abs (_, p) -> go p
  in
  go entry
  + List.fold_left (fun acc {Hflz.body; _} -> acc + go body) 0 rules
  
let should_instantiate_exists original_hes z3_path =
  let existential_quantifier_number_threthold = 3 in
  let coe1, coe2, lexico_pair_number = (1, 1, 1) in
  
  let exists_count_prover = count_exists original_hes in
  let hes_ = Hflz_mani.encode_body_exists coe1 coe2 original_hes Hflmc2_syntax.IdMap.empty [] false in
  let hes_ = Hflz_mani.elim_mu_with_rec hes_ coe1 coe2 lexico_pair_number Hflmc2_syntax.IdMap.empty false [] z3_path in
  if not @@ Hflz.ensure_no_mu_exists hes_ then failwith "elim_mu";
  is_nu_only_tractable hes_
  >>= (fun t_prover ->
    let dual_hes = Hflz_mani.get_dual_hes original_hes in
    let exists_count_disprover = count_exists dual_hes in
    let dual_hes = Hflz_mani.encode_body_exists coe1 coe2 dual_hes Hflmc2_syntax.IdMap.empty [] false  in
    let dual_hes = Hflz_mani.elim_mu_with_rec dual_hes coe1 coe2 lexico_pair_number Hflmc2_syntax.IdMap.empty false [] z3_path in
    if not @@ Hflz.ensure_no_mu_exists dual_hes then failwith "elim_mu";
    is_nu_only_tractable dual_hes
    >>| (fun t_disprover ->
      let should_instantiate =
        (not t_prover || not t_disprover) &&
          exists_count_prover <= existential_quantifier_number_threthold && exists_count_disprover <= existential_quantifier_number_threthold in
      log_string @@ "should_instantiate_exists: " ^ (string_of_bool should_instantiate) ^ " (tractable_prover=" ^ string_of_bool t_prover ^ ", tractable_disprover=" ^ string_of_bool t_disprover ^ ",exists_count_prover=" ^ string_of_int exists_count_prover ^ ", exists_count_disprover=" ^ string_of_int exists_count_disprover ^ ")";
      should_instantiate
    )
  )
  
let count_occuring (*id_type_map:(unit Hflmc2_syntax.Id.t, Manipulate.Hflz_util.variable_type, Hflmc2_syntax.IdMap.Key.comparator_witness) Base.Map.t*) hes s =
  let open Hflmc2_syntax in
  (* let ids =
    IdMap.filter id_type_map ~f:(fun ty -> match ty with VTHigherInfo _ -> true | VTVarMax _ -> false) in *)
  let s_len = String.length s in
  let rec go hflz = match hflz with
    | Hflz.Abs (v, p) -> begin
      let c = if String.length v.Id.name >= s_len && String.sub v.Id.name 0 s_len = s then 1 else 0 in
      (* let c = 
        match IdMap.find ids (Id.remove_ty v) with
        | Some _ -> 1
        | None -> 0 in *)
      c + (go p)
    end
    | Bool _ | Var _ | Arith _ | Pred _ -> 0
    | Or (p1, p2) -> go p1 + go p2
    | And (p1, p2) -> go p1 + go p2
    | App (p1, p2) -> go p1 + go p2
    | Forall (v, p1) ->
      let c = if String.length v.Id.name >= s_len && String.sub v.Id.name 0 s_len = s then 1 else 0 in
      c + (go p1)
    | Exists (_, p1) -> go p1
  in
  Hflz.merge_entry_rule hes
  |> List.map
    (fun {Hflz.body; _} ->
      go body
    )
  |> List.fold_left (fun acc c -> acc + c) 0
  
let elim_mu_exists solve_options (hes : 'a Hflz.hes) name =
  let {no_elim;
    use_all_variables;
    assign_values_for_exists_at_first_iteration; approx_parameter;_ } = solve_options in
  (* TODO: use 2nd return value of add_arguments *)
  let {coe1; coe2; add_arg_coe1; add_arg_coe2; lexico_pair_number} = approx_parameter in
  let should_add_arguments = add_arg_coe1 > 0 in
  let s_count = ref 0 in
  let t_count = ref 0 in
  
  let add_arguments hes =
    Manipulate.Add_arguments_infer_partial_application.infer solve_options.with_partial_analysis solve_options.with_usage_analysis hes add_arg_coe1 add_arg_coe2 solve_options.no_temp_files
  in
  
  if no_elim then begin
    let hes =
      if should_add_arguments then
        let hes, _, _ = add_arguments hes in
        hes
      else hes in
    [hes, [], (0, 0)]
  end else begin
    let hes, id_type_map, id_ho_map =
      if should_add_arguments then
        add_arguments hes
      else
        hes, Hflmc2_syntax.IdMap.empty, [] in
    
    let () =
      Log.info begin fun m -> m ~header:("Extra arguments added HES (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
      if not solve_options.no_temp_files then
        ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_extra_arguments_added.txt") hes
      in
    
    let () =
      let open Hflmc2_syntax in
      let strs = Hflmc2_syntax.IdMap.fold id_type_map ~init:[] ~f:(fun ~key ~data acc -> (key.Id.name ^ ": " ^ Manipulate.Hflz_util.show_variable_type data) :: acc) in
      log_string @@ "id_type_map: " ^ Hflmc2_util.show_list (fun s -> s) strs;
      log_string @@ "id_ho_map: " ^ Hflmc2_util.show_list (fun (t, id) -> "(" ^ t.Id.name ^ ", " ^ id.Id.name ^ ")") id_ho_map
      in
    
    let heses, id_type_map =
      (* (unit Id.t, Hflz_util.variable_type, Hflmc2_syntax.IdMap.Key.comparator_witness) Map.t *)
      if assign_values_for_exists_at_first_iteration && coe1 = 1 && coe2 = 1 then
        let heses = Manipulate.Hflz_manipulate_2.eliminate_exists_by_assinging coe1 hes in
        let accs = List.map (fun (_, acc) -> acc) heses |> List.flatten in
        (* for id_ho_map ? *)
        let id_type_map =
          List.fold_left
            (fun id_type_map (x, integer) ->
              Manipulate.Hflz_util.beta_id_type_map id_type_map x (Arith (Int integer))
            )
            id_type_map
            accs in
        heses, id_type_map
      else
        (log_string "AAAA"; [Hflz_mani.encode_body_exists coe1 coe2 hes id_type_map id_ho_map use_all_variables, []], id_type_map) in

    List.map (fun (hes, acc) ->
      let () =
        Log.info begin fun m -> m ~header:("Exists-Encoded HES (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
        if not solve_options.no_temp_files then
          ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_exists_encoded.txt") hes
        in

      let hes = Hflz_mani.elim_mu_with_rec hes coe1 coe2 lexico_pair_number id_type_map use_all_variables id_ho_map solve_options.z3_path in
      
      let () =
        Log.info begin fun m -> m ~header:("Eliminate Mu (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
        if not solve_options.no_temp_files then
          ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_elim_mu.txt") hes;
        if not @@ Hflz.ensure_no_mu_exists hes then failwith "elim_mu" in

      let hes =
        if should_add_arguments then
          let occuring_count = count_occuring hes Manipulate.Add_arguments_adding.extra_param_name in
          t_count := occuring_count;
          log_string @@ "occuring_count: " ^ string_of_int occuring_count;
          let occuring_count = count_occuring hes Manipulate.Add_arguments_adding.extra_arg_name in
          s_count := occuring_count;
          log_string @@ "occuring_count s: " ^ string_of_int occuring_count;
          hes
        else
          hes
      in
      hes, acc, (!t_count, !s_count)
    ) heses
  end

exception Exit

let summarize_results (results : (Status.t * 'a) list) =
  let non_fail_results = List.filter (fun (r, _) -> match r with Status.Fail -> false | _ -> true) results in
  if (List.length non_fail_results == 0)
  then Status.Fail, List.map snd results
  else begin
    let results = non_fail_results in
    let contains_invalid = List.length @@ List.filter (fun (r, _) -> match r with Status.Invalid -> true | _ -> false) results <> 0 in
    let contains_valid = List.length @@ List.filter (fun (r, _) -> match r with Status.Valid -> true | _ -> false) results <> 0 in
    (* priotize "valid" when parallel solving of instantiate eixsts *)
    (* if contains_invalid && contains_valid then assert false; *)
    if contains_valid then Status.Valid, results |> List.filter_map (fun (r, d) -> match r with Status.Valid -> Some d | _ -> None)
    else if contains_invalid then Status.Invalid, results |> List.filter_map (fun (r, d) -> match r with Status.Invalid -> Some d | _ -> None)
    else Status.Unknown, List.map snd results
  end

let get_next_approx_parameter ?param ?(iter_count=0) with_add_arguments =
  let coeffs = 
    if with_add_arguments then
      [
        (* (1, 1,  0, 0, 1); (* 1 *)
        (1, 8,  0, 0, 1); (* 2 *)
        (4, 32, 0, 0, 1); (* 3 *)
        (1, 1,  1, 0, 1); (* 4 *)
        (2, 1,  1, 0, 1); (* 5 *)
        (1, 1,  2, 0, 1); (* 6 *)
        (1, 8,  2, 1, 1); (* 7 *)
        (1, 8,  2, 1, 2); (* 8 *)
         *)
        (1, 1, 1, 1, 1);
        (1, 1, 1, 1, 2);
        (1, 8, 1, 1, 1);
        (1, 8, 1, 1, 2);
      ]
    else
      [
        (1, 1,  0, 0, 1);
        (1, 1,  0, 0, 2);
        (1, 8,  0, 0, 1);
        (2, 16, 0, 0, 1);
        (2, 16, 0, 0, 2);
      ] in
  match List.nth_opt coeffs iter_count with
  | Some (coe1, coe2, add_arg_coe1, add_arg_coe2, lexico_pair_number) ->
    {
      coe1 = coe1;
      coe2 = coe2;
      add_arg_coe1 = add_arg_coe1;
      add_arg_coe2 = add_arg_coe2;
      lexico_pair_number = lexico_pair_number;
    }
  | None -> begin
    let param = Option.get param in
    if param.lexico_pair_number = 1 then
      { param with
        lexico_pair_number = 2;
      }
    else
      {
        coe1 = param.coe1 * 2;
        coe2 = param.coe2 * 2;
        add_arg_coe1 = param.add_arg_coe1 * 2;
        add_arg_coe2 = param.add_arg_coe2 * 2;
        lexico_pair_number = 1;
      }
  end

let merge_debug_contexts cs_ =
  match cs_ with 
  | c::cs -> begin
    List.iter
      (fun c' ->
        assert (c.mode = c'.mode);
        assert (c.iter_count = c'.iter_count);
        assert (c.coe1 = c'.coe1);
        assert (c.coe2 = c'.coe2);
        assert (c.add_arg_coe1 = c'.add_arg_coe1);
        assert (c.add_arg_coe2 = c'.add_arg_coe2);
        assert (c.file = c'.file);
        assert (c.default_lexicographic_order = c'.default_lexicographic_order);
        assert (c.t_count = c'.t_count);
        assert (c.s_count = c'.s_count);
        assert (c.elapsed_all = c'.elapsed_all);
        assert (c.will_try_weak_subtype = c'.will_try_weak_subtype)
      )
      cs;
    {
      mode = c.mode;
      iter_count = c.iter_count;
      coe1 = c.coe1;
      coe2 = c.coe2;
      add_arg_coe1 = c.add_arg_coe1;
      add_arg_coe2 = c.add_arg_coe2;
      pid = -1;
      file = c.file;
      backend_solver = None;
      default_lexicographic_order = c.default_lexicographic_order;
      exists_assignment = None;
      temp_file = String.concat "," (List.map (fun c -> c.temp_file) cs_);
      t_count = c.t_count;
      s_count = c.s_count;
      elapsed_all = c.elapsed_all;
      will_try_weak_subtype = c.will_try_weak_subtype;
    }
  end
  | [] -> assert false

(* これ以降、本プログラム側での近似が入る *)
let rec mu_elim_solver ?(was_weak_subtype_used=false) ?(cached_formula=None) iter_count (solve_options : Solve_options.options) hes mode_name iter_count_offset =
  Hflz_mani.simplify_bound := solve_options.simplify_bound;
  let nu_only_heses =
    match cached_formula with
    | None -> elim_mu_exists solve_options hes mode_name
    | Some p -> p in
  let approx_param = solve_options.approx_parameter in
  let will_try_weak_subtype = solve_options.try_weak_subtype && not was_weak_subtype_used in
  let debug_context_ = {
    mode = mode_name;
    iter_count = iter_count;
    coe1 = approx_param.coe1;
    coe2 = approx_param.coe2;
    add_arg_coe1 = approx_param.add_arg_coe1;
    add_arg_coe2 = approx_param.add_arg_coe2;
    pid = solve_options.pid;
    file = solve_options.file;
    backend_solver = None;
    default_lexicographic_order = approx_param.lexico_pair_number;
    exists_assignment = None;
    temp_file = "";
    t_count = -1;
    s_count = -1;
    elapsed_all = -1.0;
    will_try_weak_subtype = will_try_weak_subtype;
  } in
  (* e.g. solvers = [(* an instantiation of variables quantified by exists, e.g. x1 = 0 *)[solve with hoice, solve with z3]; (* x1 = 1*)[solve with hoice, solve with z3]]
    For each instantiation, if both hoice and z3 returned "fail," then the overall result is "fail."
    If either of hoice and z3 returned some result other than "fail," then the result of the current iteration is the result returned by the solvers.
    If one of instantiation of existential variables has returned "valid," then result of current iteration is "valid."
  *)
  let (solvers: (Status.t * debug_context) Deferred.t list list) = 
    match solve_options.backend_solver with
    | None ->
      List.map (fun (nu_only_hes, exists_assignment, (t_count, s_count)) ->
        let debug_context_ = {debug_context_ with t_count; s_count} in
        [
          solve_onlynu_onlyforall
            { solve_options with backend_solver = Some "hoice" }
            ({ debug_context_ with backend_solver = Some "hoice"; exists_assignment = Some exists_assignment })
            nu_only_hes
            false
            false
            will_try_weak_subtype;
          solve_onlynu_onlyforall
            { solve_options with backend_solver = Some "z3" }
            ({ debug_context_ with backend_solver = Some "z3"; exists_assignment = Some exists_assignment })
            nu_only_hes
            false
            true (* if the formula is intractable in katsura-solver, stop either of the two solving processes to save computational resources *)
            will_try_weak_subtype
        ]
      ) nu_only_heses
    | Some _ ->
      List.map (fun (nu_only_hes, _, (t_count, s_count)) -> [solve_onlynu_onlyforall solve_options {debug_context_ with t_count; s_count} nu_only_hes false false false]) nu_only_heses in
  let (is_valid : (Status.t * debug_context list) list Ivar.t) = Ivar.create () in
  let deferred_is_valid = Ivar.read is_valid in
  let (deferred_all : (Status.t * debug_context list) list Deferred.t) =
    Deferred.all (
      List.map (fun s ->
        let mixed_solvers_result = Ivar.create () in
        let deferred_mixed_solvers_result = Ivar.read mixed_solvers_result in
        let s = List.map (fun s_ ->
          s_ >>| (fun (result, d) ->
            (match result with
            | Status.Valid | Status.Invalid | Status.Unknown -> begin
              (* result of current iteration has determined *)
              if Ivar.is_empty mixed_solvers_result
                then Ivar.fill mixed_solvers_result [(result, d)]
                else ()
            end
            | Status.Fail -> ());
            (result, d)
          )
        ) s in
        (Deferred.any [Deferred.all s; deferred_mixed_solvers_result]) >>|
        (fun results ->
          let result, d = summarize_results results in
          (match result with
          | Status.Valid ->
            (* if one of instantiation of existential variables has returned "valid," then result of current iteration is "valid" *)
            if Ivar.is_empty is_valid
              then Ivar.fill is_valid [(result, d)]
              else ()
          | _ -> ());
          (result, d)
        )
      )
      solvers
    ) in
  let start_time_all = Unix.gettimeofday () in
  Deferred.any [deferred_is_valid; deferred_all]
  >>= (fun results -> kill_processes (debug_context_.mode)
  >>= (fun _ ->
      let elapsed_all = Unix.gettimeofday () -. start_time_all in
      let result, debug_contexts = summarize_results results in
      let debug_contexts = List.flatten debug_contexts in
      let debug_contexts =
        List.map (fun d -> {d with elapsed_all}) debug_contexts in
      if not solve_options.no_temp_files then
        merge_debug_contexts debug_contexts |> output_post_merged_debug_info;
      let retry approx_param =
        if !has_solved then
          return (Status.Unknown, debug_contexts)
        else begin
          if will_try_weak_subtype then begin
            mu_elim_solver ~was_weak_subtype_used:true ~cached_formula:(Some nu_only_heses) iter_count solve_options hes mode_name iter_count_offset
          end else begin
            let approx_param = get_next_approx_parameter ~param:approx_param ~iter_count:(iter_count + iter_count_offset) solve_options.add_arguments in
            let solve_options = { solve_options with approx_parameter = approx_param } in
            mu_elim_solver (iter_count + 1) solve_options hes mode_name iter_count_offset
          end
        end
      in
      match result with
      | Status.Valid -> return (Status.Valid, debug_contexts)
      | Status.Invalid ->
        if solve_options.oneshot then return (Status.Invalid, debug_contexts)
        else retry approx_param
      | Status.Unknown ->
        if not solve_options.stop_on_unknown then (
          message_string ~header:"Result" @@ "return Unknown (" ^ show_debug_contexts debug_contexts ^ ")";
          if solve_options.oneshot then return (Status.Unknown, debug_contexts)
          else retry approx_param
        ) else return (Status.Unknown, debug_contexts)
      | Status.Fail -> return (Status.Fail, debug_contexts)))

let check_validity_full (solve_options : Solve_options.options) hes iter_count_offset =
  let hes_for_disprove = Hflz_mani.get_dual_hes hes in
  let deferreds =
    [ mu_elim_solver 1 solve_options hes "prover" iter_count_offset;
      (mu_elim_solver 1 solve_options hes_for_disprove "disprover" iter_count_offset >>| (fun (s, i) -> Status.flip s, i)) ] in
  let dresult = Deferred.any deferreds in
  dresult >>=
    (fun ri ->
      has_solved := true; (* anyでいずれかがdetermineしても全てのdeferredがすぐに停止するとは限らない(？)ため、dualのソルバを停止させる *)
      kill_processes "prover" >>=
        (fun _ -> kill_processes "disprover" >>|
          (fun _ -> ri)
        )
    )

let check_validity_full_oneshot (solve_options : Solve_options.options) hes =
  let hes_for_disprove = Hflz_mani.get_dual_hes hes in
  let deferreds =
    [ mu_elim_solver 1 solve_options hes "prover" 0;
      mu_elim_solver 1 solve_options hes_for_disprove "disprover" 0] in
  let dresult =
    let deferred_got_result = Ivar.create () in
    let deferred_deferred_got_result = Ivar.read deferred_got_result in
    let deferred_wait_all = 
      deferreds
      |> List.map
        (fun deferred ->
          deferred >>| (fun ri ->
            (match ri with
            | (Status.Valid, _) ->
              if Ivar.is_empty deferred_got_result
                then Ivar.fill deferred_got_result [ri]
                else ()
            | _ -> ());
            ri
          )
        )
      |> Deferred.all in
    Deferred.any [deferred_wait_all; deferred_deferred_got_result]
    >>|
    (fun ris ->
      match ris with
      | [ri] -> begin
        log_string "with deferred_got_result";
        let {mode;_ } = List.hd @@ snd ri in
        match mode with
        | "prover" -> ri
        | "disprover" ->
          let (s, d) = ri in
          (Status.flip s, d)
        | _ -> assert false
      end
      | [prover_ri; disprover_ri] -> begin
        match fst prover_ri, fst disprover_ri with
        | Status.Valid, Status.Valid -> assert false
        | Status.Valid, _ -> prover_ri
        | _, Status.Valid ->
          let (s, d) = disprover_ri in
          (Status.flip s, d)
        (* ad-hoc *)
        | Status.Fail, _ -> prover_ri
        | _, Status.Fail -> disprover_ri
        | Status.Invalid, _ -> (Status.Unknown, snd prover_ri)
        | _, Status.Invalid -> (Status.Unknown, snd disprover_ri)
        | _ -> (Status.Unknown, snd prover_ri)
      end
      | _ -> assert false
    ) in
  dresult >>=
    (fun ri ->
      has_solved := true; (* anyでいずれかがdetermineしても全てのdeferredがすぐに停止するとは限らない(？)ため、dualのソルバを停止させる *)
      kill_processes "prover" >>=
        (fun _ -> kill_processes "disprover" >>|
          (fun _ -> ri)
        )
    )

let check_validity_full_entry solve_options hes iter_count_offset =
  if solve_options.oneshot then check_validity_full_oneshot solve_options hes else check_validity_full solve_options hes iter_count_offset

let solve_onlynu_onlyforall_with_schedule (solve_options : Solve_options.options) nu_only_hes =
  let solve_options =
    { solve_options with
      no_elim = true; no_disprove = false; oneshot = true } in
  let dresult = mu_elim_solver 1 solve_options nu_only_hes "solver" 0 in
  dresult >>=
    (fun ri -> kill_processes "solver" >>|
        (fun _ -> ri))
  
(* let solve_onlynu_onlyforall_with_schedule solve_options nu_only_hes cont =
  let dresult = Deferred.any [solve_onlynu_onlyforall { solve_options with no_disprove = false } None nu_only_hes true >>| (fun (s, _) -> s)] in
  upon dresult (fun result -> cont (result, [None]); Rfunprover.Solver.kill_z3(); shutdown 0);
  Core.never_returns(Scheduler.go()) *)
  
(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity solve_options (hes : 'a Hflz.hes) cont =
  let solve_options, iter_count_offset =
    if solve_options.use_custom_parameter then  
      solve_options, 0
    else
      let iter_count_offset = if solve_options.always_add_arguments then 3 else 0 in
      let initial_param =
        get_next_approx_parameter solve_options.add_arguments ~iter_count:(0 + iter_count_offset) in
      { solve_options with approx_parameter = initial_param }, iter_count_offset in
  
  let dresult =
    (if solve_options.auto_existential_quantifier_instantiation && not solve_options.assign_values_for_exists_at_first_iteration then
      should_instantiate_exists hes solve_options.z3_path
      >>| (fun f ->
        if f then { solve_options with assign_values_for_exists_at_first_iteration = true } else solve_options
      )
    else
      return solve_options)
    >>= (fun solve_options ->
      if solve_options.always_approximate then
        check_validity_full_entry solve_options hes iter_count_offset
      else begin
        if is_onlynu_onlyforall hes then
          solve_onlynu_onlyforall_with_schedule solve_options hes
        else if is_onlymu_onlyexists hes then
          solve_onlynu_onlyforall_with_schedule solve_options (Hflz_mani.get_dual_hes hes)
          >>| (fun (status_pair, i) -> (Status.flip status_pair, i))
        else check_validity_full_entry solve_options hes iter_count_offset
      end
    ) in
  upon dresult (
    fun (result, info) ->
      cont (result, info);
      shutdown 0);
  Core.never_returns(Scheduler.go())

(* 
CheckValidity(Φ, main) { /* Φ: HES, main: Entry formula */
  if Φ is a ν-only HES then return solve(Φ,main)
  else if Φ is a µ-only HES then return not(solve(MakeDual(Φ,main)))
  else return (CheckSub(Φ, main) || not(CheckSub(MakeDual(Φ,main)));
}
CheckSub(Φ, main){
  (Φ_0 ,main0 ) := ElimMu(Φ,main)
  while(true) {
    if solve(Φ_0 ,main0) then return true
    else (Φ_0 ,main0 ) := IncreaseBounds(Φ_0 ,main0);
  }
}
*)
