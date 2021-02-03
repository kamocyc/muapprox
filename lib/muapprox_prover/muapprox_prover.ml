module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status
module Solve_options = Solve_options
module Hflz_mani = Manipulate.Hflz_manipulate
module Hflz_convert = Hflz_convert
module Hflz_convert_rev = Hflz_convert_rev
module Check_formula_equality = Check_formula_equality
module Abbrev_variable_numbers = Abbrev_variable_numbers

let read_strings file =
  let fp = open_in file in
  let rec loop() =
    try
      let s = input_line fp in (s::loop())
    with _ -> close_in fp; []
  in loop()

open Async
open Solve_options

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

type debug_context = {
  coe1: int;
  coe2: int;
  iter_count: int;
  mode: string;
  pid: int;
  file: string;
}

let show_debug_context debug =
  match debug with
  | None -> ""
  | Some debug -> "(mode=" ^ debug.mode ^ ", iter_count=" ^ string_of_int debug.iter_count ^ ", coe1=" ^ (string_of_int debug.coe1) ^ ", coe2=" ^ (string_of_int debug.coe2) ^ ")"


let kill_processes () =
  (* eld and java are not executed when ran with --no-disprove because they are used only for proving unsat *)
  (* TODO: main.exe should be renamed *)
  let process_names = ["hflmc2"; "main.exe"; "z3"; "hoice"] in
  let kill_command = String.concat "; " (List.map (fun n -> "pkill " ^ n) process_names) in
  print_endline @@ "kill command=" ^ kill_command;
  Unix.system kill_command
  
let save_string_to_file path buf =
  let oc = Stdlib.open_out path in
  Stdlib.output_string oc buf;
  Stdlib.close_out oc
      
let output_debug (dbg : debug_context option) path =
  let tos = string_of_int in
  match dbg with
  | Some dbg -> begin
    save_string_to_file (dbg.mode ^ ".tmp") (dbg.mode ^ "," ^ tos dbg.pid ^ "," ^ tos dbg.iter_count ^ "," ^ tos dbg.coe1 ^ "," ^ tos dbg.coe2 ^ "," ^ path ^ "," ^ dbg.file)
  end
  | None -> ()
  

module type BackendSolver = sig
  val run : options -> debug_context option -> Hflmc2_syntax.Type.simple_ty Hflz.hes -> bool -> Status.t Deferred.t
end

(* TODO: 引用符で囲むなどの変換する？ *)
let unix_system commands =
  let r = Random.int 0x10000000 in
  let stdout_name, stderr_name = Printf.sprintf "/tmp/%d_stdout.tmp" r, Printf.sprintf "/tmp/%d_stderr.tmp" r in
  let commands = Array.concat [commands; [|">"; stdout_name; "2>"; stderr_name|]] in
  let command = String.concat " " (Array.to_list commands) in
  print_endline @@ "run command (unix_system): " ^ command;
  let start_time = Stdlib.Sys.time () in
  Unix.system command 
    >>| (fun code ->
      let unlines lines = String.concat "\n" lines in
      let elapsed = Stdlib.Sys.time () -. start_time in
      code, elapsed,
      read_strings stdout_name |> unlines,
      read_strings stderr_name |> unlines
    )

module FptProverRecLimitSolver : BackendSolver = struct
  let convert_status (s : Fptprover.Status.t) : Status.t =
    match s with
    | Valid -> Valid
    | Invalid -> Invalid
    | Unknown -> Unknown
    | Sat -> Sat
    | UnSat -> UnSat
  
  let run option debug_context (hes : 'a Hflz.hes) with_par =
    print_endline "FIRST-ORDER";
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes in
    print_endline @@ "HES PATH: " ^ path_;
    let hes = Hflz_convert_rev.of_hes hes in
    print_endline @@ "Converted Hes: " ^ Convert.Hesutil.str_of_hes hes;
    let hes' = Hflz_convert.of_hes hes in
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes' in
    print_endline @@ "HES PATH 2: " ^ path_;
    output_debug debug_context path_;
    (* Global.config := Config.update_hoice true Global.config; *)
    (* 1, 2番目の引数は使われていない *)
    if with_par then
      Rfunprover.Solver.solve_onlynu_onlyforall_par false (int_of_float option.timeout) option.print_for_debug hes
        >>| (fun status -> convert_status status)
    else
      Rfunprover.Solver.solve_onlynu_onlyforall_z3 true (int_of_float option.timeout) option.print_for_debug hes 
        >>| (fun status -> convert_status status)
end

module SolverCommon = struct
  let output_pre_debug_info hes debug_context =
    let path' = 
      match debug_context with 
      | Some debug_context ->
        let file = Filename.basename debug_context.file ^ "__" ^ debug_context.mode ^ "__" ^ string_of_int debug_context.iter_count ^ ".in" in
        Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:file ~without_id:true true hes 
      | None ->
        Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:true true hes in
    print_string @@ "HES for backend " ^ (show_debug_context debug_context) ^ ": ";
    print_endline path';
    output_debug debug_context path'
  
  type temp_result_type =
    | TValid
    | TInvalid
    | TUnknown
    | TTerminated
    | TError
  
  let to_string_result = function
    | TValid -> "valid"
    | TInvalid -> "invalid"
    | TUnknown -> "unknown"
    | TTerminated -> "terminated"
    | TError -> "error"
    
  let output_post_debug_info tmp_res elapsed stdout stderr debug_context =
    let open Yojson in
    let data = 
      `Assoc (List.concat [[
        ("result", `String (to_string_result tmp_res));
        ("time", `Float elapsed);
        ("stdout", `String stdout);
        ("stderr", `String stderr);];
        match debug_context with
        | None -> []
        | Some debug_context ->
          [("file", `String debug_context.file);
          ("mode", `String debug_context.mode);
          ("iter_count", `Int debug_context.iter_count);
          ("coe1", `Int debug_context.coe1);
          ("coe2", `Int debug_context.coe2);
          ("pid", `Int debug_context.pid)]
        ]) in
    let mode_string = match debug_context with | None -> "none" | Some d -> d.mode in
    let oc = Stdio.Out_channel.create ~append:true ("post_" ^ mode_string ^ ".tmp") in
    Basic.pretty_to_channel oc data;
    Stdio.Out_channel.close oc
    
  let parse_results_inner (exit_status, stdout, stderr) debug_context elapsed status_parser =
    let res, tmp_res = 
      match exit_status with 
      | Ok () -> begin
        let status = status_parser stdout in
        print_endline @@ "Parsed status: " ^ Status.string_of status ^ " " ^ (show_debug_context debug_context);
        status, (
        match status with
        | Valid -> TValid
        | Invalid -> TInvalid
        | _ -> TUnknown)
      end
      | Error (`Exit_non_zero 143) -> begin
        print_endline @@ "Terminated " ^ (show_debug_context debug_context);
        Status.Unknown, TTerminated
      end
      | _ -> begin
        print_endline "error status";
        Status.Unknown, TError
      end in
    output_post_debug_info tmp_res elapsed stdout stderr debug_context;
    print_endline @@ Status.string_of res;
    res
end

module KatsuraSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "katsura_solver_path" with
    | None -> failwith "Please set environment variable `katsura_solver_path`"
    | Some s -> s
  
  let save_hes_to_file hes debug_context =
    output_pre_debug_info hes debug_context;
    let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:true true hes in
    (* print_endline @@ "FILE: " ^ path; *)
    path
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path :: (if solver_options.no_disprove then ["--no-disprove"] else []) @
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None;
          match solver_options.solver_backend with None -> None | Some s -> Some ("--solver=" ^ s)]) @
        [hes_path]
    )

  let parse_results result debug_context elapsed =
    parse_results_inner result debug_context elapsed (fun stdout -> 
      (* print_endline @@ "stdout::" ^ show_debug_context debug_context;
      print_endline stdout;
      print_endline "stdout_end::"; *)
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nProfiling:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        Status.of_string @@ Str.matched_group 2 stdout
      with
        | Not_found -> failwith @@ "not matched"
    )
    
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let command = solver_command path solve_options in
    unix_system command >>|
      (fun (status_code, elapsed, stdout, stderr) ->
        try
          parse_results (status_code, stdout, stderr) debug_context elapsed
        with _ -> Status.Unknown)
end

module IwayamaSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "iwayama_solver_path" with
    | None -> failwith "Please set environment variable `iwayama_solver_path`"
    | Some s -> s
  
  let save_hes_to_file hes debug_context =
    let hes = Manipulate.Hflz_manipulate.encode_body_forall_except_top hes in
    output_pre_debug_info hes debug_context;
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:true false hes
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path::
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None;
          match solver_options.solver_backend with None -> None | Some s -> Some ("--solver=" ^ s)]) @
        [hes_path]
    )

  let parse_results result debug_context elapsed =
    parse_results_inner result debug_context elapsed (fun stdout -> 
      (* Verification Result: の行を探す。 *)
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nLoop Count:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        Status.of_string @@ Str.matched_group 2 stdout
      with
        | Not_found -> failwith @@ "not matched"
    )
  
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let command = solver_command path solve_options in
    unix_system command
    >>| (fun (status_code, elapsed, stdout, stderr) ->
        try
          parse_results (status_code, stdout, stderr) debug_context elapsed
          with _ -> Status.Unknown)
end

let rec is_first_order_function_type (ty : Hflmc2_syntax.Type.simple_ty) =
  match ty with
  | TyBool () -> true
  | TyArrow (ty1, ty2) -> 
    ty1.ty = TyInt && is_first_order_function_type ty2
  
let is_first_order_hes hes =
  Hflz_mani.decompose_lambdas_hes hes
  |> (fun (e, r) -> (Hflz.mk_entry_rule e)::r)
  |> List.for_all (fun { Hflz.var; _} -> is_first_order_function_type var.ty)
  
let solve_onlynu_onlyforall solve_options debug_context hes with_par =
  let hes =
    if solve_options.no_simplify then hes else (let hes = Manipulate.Hes_optimizer.simplify hes in Log.app begin fun m -> m ~header:("Simplified") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end; hes) in
  (* let hes = Abbrev_variable_numbers.abbrev_variable_numbers_hes hes in *)
  let run =
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      FptProverRecLimitSolver.run
    ) else (
      match solve_options.solver with
      | Katsura -> KatsuraSolver.run
      | Iwayama -> IwayamaSolver.run
    ) in
  run solve_options debug_context hes with_par

let flip_solver solver =
  fun timeout is_print_for_debug ->
  let status, original_status = solver timeout is_print_for_debug in
  Status.flip status, original_status
  
let fold_hflz folder phi init =
  let rec go phi acc = match phi with
    | Hflz.Bool   _ -> folder acc phi 
    | Hflz.Var    _ -> folder acc phi
    | Hflz.Or (f1, f2)  -> folder acc phi |> go f1 |> go f2
    | Hflz.And (f1, f2) -> folder acc phi |> go f1 |> go f2
    | Hflz.Abs (x, f1)  -> folder acc phi |> go f1
    | Hflz.Forall (x, f1) -> folder acc phi |> go f1
    | Hflz.Exists (x, f1) -> folder acc phi |> go f1
    | Hflz.App (f1, f2)   -> folder acc phi |> go f1 |> go f2
    | Hflz.Arith t -> folder acc phi
    | Hflz.Pred (p, args) -> folder acc phi in
  go phi init

(* let is_not_recursive rec_preds var = not @@ List.exists (Hflmc2_syntax.Id.eq var) rec_preds *)
(* let to_greatest_from_not_recursive rec_preds =
  List.map
    (fun ({Hflz.var; _} as rule) ->
      if is_not_recursive rec_preds var
      then { rule with fix = Fixpoint.Greatest}
      else rule) *)

let is_onlyforall_body formula =
  fold_hflz (fun b f -> match f with Hflz.Exists _ -> false | _ -> b) formula true
let is_onlynu_onlyforall_rule {Hflz.var; fix; body} =
  (fix = Fixpoint.Greatest) && is_onlyforall_body body
let is_onlynu_onlyforall (entry, rules) =
  is_onlyforall_body entry
  && (List.for_all is_onlynu_onlyforall_rule rules)

let is_onlyexists_body formula =
  fold_hflz (fun b f -> match f with Hflz.Forall _ -> false | _ -> b) formula true
let is_onlymu_onlyexists_rule {Hflz.var; fix; body} =
  (fix = Fixpoint.Least) && is_onlyexists_body body
let is_onlymu_onlyexists (entry, rules) =
  is_onlyexists_body entry
  && (List.for_all is_onlymu_onlyexists_rule rules)

(* let flip_status_pair (s1, s2) =
  (Status.flip s1, s2) *)

(* TODO: forallを最外に移動？ => いらなそうか *)
let elim_mu_exists coe1 coe2 debug_output (hes : 'a Hflz.hes) name =
  (* 再帰参照していない述語はgreatestに置換 *)
  (* これをすると、fixpoint alternationが新たにできて、式が複雑になることがあるので、やめる *)
  (* let hes = to_greatest_from_not_recursive rec_preds hes in *)
  (* forall, existential, nu, mu *)
  (* forall, nu, mu *)
  let hes = Hflz_mani.encode_body_exists coe1 coe2 hes in
  if debug_output then Log.app begin fun m -> m ~header:("Exists-Encoded HES (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
  (* if debug_output then ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_exists_encoded.txt") hes; *)
  let hes = Hflz_mani.elim_mu_with_rec hes coe1 coe2 in
  if debug_output then Log.app begin fun m -> m ~header:("Eliminate Mu (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
  if not @@ Hflz.ensure_no_mu_exists hes then failwith "elim_mu";
  (* if debug_output then ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_elim_mu.txt") hes; *)
  (* forall, nu *)
  hes

(* これ以降、本プログラム側での近似が入る *)
let rec mu_elim_solver coe1 coe2 iter_count (solve_options : Solve_options.options) debug_output hes mode_name = 
  let nu_only_hes = elim_mu_exists coe1 coe2 debug_output hes mode_name in
  let debug_context = Some {
    mode = mode_name;
    iter_count = iter_count;
    coe1 = coe1;
    coe2 = coe2;
    pid = solve_options.pid;
    file = solve_options.file;
  } in
  if not solve_options.dry_run then (
    let solvers = 
      match solve_options.solver_backend with
      | None -> [
        solve_onlynu_onlyforall { solve_options with solver_backend = Some "hoice" } debug_context nu_only_hes false;
        solve_onlynu_onlyforall { solve_options with solver_backend = Some "z3" } debug_context nu_only_hes false
      ]
      | Some s -> [solve_onlynu_onlyforall solve_options debug_context nu_only_hes false] in
    (Deferred.any solvers)
    >>= (fun result ->
      (if solve_options.kill_processes then kill_processes () >>= (fun _ -> Deferred.return None) else Deferred.return None)
    >>= (fun _ ->
        match result with
        | Status.Valid -> return (Status.Valid, debug_context)
        | Status.Invalid ->
          let (coe1',coe2') = if (coe1,coe2)=(1,1) then (1,8) else (2*coe1, 2*coe2) in
          mu_elim_solver coe1' coe2' (iter_count + 1) solve_options false hes mode_name
        | Status.Unknown -> 
          if solve_options.ignore_unknown then (
            print_endline @@ "return Unknown (" ^ show_debug_context debug_context ^ ")";
            let (coe1',coe2') = if (coe1,coe2)=(1,1) then (1,8) else (2*coe1, 2*coe2) in
            mu_elim_solver coe1' coe2' (iter_count + 1) solve_options false hes mode_name
          ) else return (Status.Unknown, debug_context)
        | _ -> return (Status.Unknown, debug_context)))
  ) else (print_endline "DRY RUN"; Unix.system "echo" >>| (fun _ -> Status.Unknown, None))

let check_validity_full coe1 coe2 solve_options hes cont =
  let hes_for_disprove = Hflz_mani.get_dual_hes hes in
  let dresult = Deferred.any
                  [mu_elim_solver coe1 coe2 1 solve_options solve_options.print_for_debug hes "prover";
                   (mu_elim_solver coe1 coe2 1 solve_options solve_options.print_for_debug hes_for_disprove "disprover" >>| (fun (s, i) -> Status.flip s, i))] in
  upon dresult (
    fun (result, info) ->
      cont (result, info);
      Rfunprover.Solver.kill_z3();
      shutdown 0);
  Core.never_returns(Scheduler.go())

let solve_onlynu_onlyforall_with_schedule solve_options nu_only_hes cont =
  let dresult = Deferred.any [solve_onlynu_onlyforall { solve_options with no_disprove = false } None nu_only_hes true] in
  upon dresult (fun result -> cont (result, None); Rfunprover.Solver.kill_z3(); shutdown 0);
  Core.never_returns(Scheduler.go())
  
(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity coe1 coe2 solve_options (hes : 'a Hflz.hes) cont =
  if is_onlynu_onlyforall hes then
    solve_onlynu_onlyforall_with_schedule solve_options hes cont
  else if is_onlymu_onlyexists hes then
    solve_onlynu_onlyforall_with_schedule solve_options (Hflz_mani.get_dual_hes hes) (fun (status_pair, i) -> cont (Status.flip status_pair, i))
  else check_validity_full coe1 coe2 solve_options hes cont

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
