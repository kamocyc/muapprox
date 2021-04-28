module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status
module Solve_options = Solve_options
module Hflz_mani = Manipulate.Hflz_manipulate
module Hflz_convert = Hflz_convert
module Hflz_convert_rev = Hflz_convert_rev
module Check_formula_equality = Check_formula_equality
module Abbrev_variable_numbers = Abbrev_variable_numbers

open Async
open Solve_options
open Unix_command

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

type debug_context = {
  coe1: int;
  coe2: int;
  iter_count: int;
  mode: string;
  pid: int;
  file: string;
  temp_file: string;
  solver_backend: string option;
  default_lexicographic_order: int;
  exists_assignment: (unit Hflz_convert_rev.Id.t * int) list option;
}

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
  
let show_debug_context debug =
  match debug with
  | None -> ""
  | Some debug ->
    let show assoc =
      let rec go = function 
        | [] -> []
        | (k, v)::xs -> (k ^ "=" ^ v)::(go xs) in
      "(" ^ (go assoc |> String.concat ", ") ^ ")"
    in
    let soi = string_of_int in
    let unwrap_or alt opt = match opt with None -> alt | Some s -> s in
    show [
      ("mode", debug.mode);
      ("iter_count", soi debug.iter_count);
      ("coe1", soi debug.coe1);
      ("coe2", soi debug.coe2);
      ("solver_backend", unwrap_or "-" debug.solver_backend);
      ("default_lexicographic_order", string_of_int debug.default_lexicographic_order);
      ("exists_assignment", Option.map (fun m -> "[" ^ ((List.map (fun (id, v) -> id.Hflmc2_syntax.Id.name ^ "=" ^ string_of_int v) m) |> String.concat "; ") ^ "]") debug.exists_assignment |> unwrap_or "-");
      ("temp_file", debug.temp_file);
    ]

let show_debug_contexts debugs =
  List.map
    (fun debug ->
      show_debug_context debug
    )
    debugs |>
  String.concat ", "
  
module type BackendSolver = sig
  val run : options -> debug_context option -> Hflmc2_syntax.Type.simple_ty Hflz.hes -> bool -> Status.t Deferred.t
end

module FptProverRecLimitSolver : BackendSolver = struct
  let convert_status (s : Fptprover.Status.t) : Status.t =
    match s with
    | Valid -> Valid
    | Invalid -> Invalid
    | Unknown -> Unknown
    | Sat | UnSat -> assert false
  
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
        let hes = Abbrev_variable_numbers.abbrev_variable_numbers_hes hes in
        let file = Filename.basename debug_context.file ^ "__" ^ debug_context.mode ^ "__" ^ string_of_int debug_context.iter_count ^ ".in" in
        Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:file ~without_id:true true hes 
      | None ->
        Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false true hes in
    print_string @@ "HES for backend " ^ (show_debug_context debug_context) ^ ": ";
    print_endline path';
    output_debug debug_context path'
  
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
      | Error (`Exit_non_zero 128) -> begin
        (* why 128? *)
        print_endline @@ "Terminated (128) " ^ (show_debug_context debug_context);
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
    let path = Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false true hes in
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
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nProfiling:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        Status.of_string @@ Str.matched_group 2 stdout
      with
        | Not_found -> failwith @@ "not matched"
    )
    
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let debug_context = Option.map (fun d -> { d with temp_file = path }) debug_context in
    let command = solver_command path solve_options in
    unix_system command (Option.map (fun c -> c.mode) debug_context) >>|
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
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false false hes
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      solver_path::
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None]) @
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
    let debug_context = Option.map (fun d -> { d with temp_file = path }) debug_context in
    let command = solver_command path solve_options in
    unix_system command (Option.map (fun c -> c.mode) debug_context)
    >>| (fun (status_code, elapsed, stdout, stderr) ->
        try
          parse_results (status_code, stdout, stderr) debug_context elapsed
          with _ -> Status.Unknown)
end

module SuzukiSolver : BackendSolver = struct
  include SolverCommon
  
  let get_solver_path () =
    match Stdlib.Sys.getenv_opt "suzuki_solver_path" with
    | None -> failwith "Please set environment variable `suzuki_solver_path`"
    | Some s -> s
  
  let save_hes_to_file hes debug_context =
    Hflmc2_syntax.Print.global_not_output_zero_minus_as_negative_value := true;
    let hes = Manipulate.Hflz_manipulate.encode_body_forall_except_top hes in
    output_pre_debug_info hes debug_context;
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~without_id:false false hes
    
  let solver_command hes_path solver_options =
    let solver_path = get_solver_path () in
    Array.of_list (
      "RUST_LOG=\" \" "::
      solver_path::
        (List.filter_map (fun x -> x)
          [if solver_options.no_backend_inlining then Some "--no-inlining" else None]) @
        [hes_path]
    )

  let parse_results result debug_context elapsed =
    parse_results_inner result debug_context elapsed (fun stdout -> 
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
        )
      with
        | Not_found -> failwith @@ "not matched"
    )
  
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let debug_context = Option.map (fun d -> { d with temp_file = path }) debug_context in
    let command = solver_command path solve_options in
    unix_system ~no_quote:true command (Option.map (fun c -> c.mode) debug_context)
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
  |> (fun hes -> Hflz.merge_entry_rule hes)
  |> List.for_all (fun { Hflz.var; _} -> is_first_order_function_type var.ty)
  
let solve_onlynu_onlyforall solve_options debug_context hes with_par =
  let hes =
    if solve_options.no_simplify
    then hes
    else (
      let hes = Manipulate.Hes_optimizer.simplify hes in
      Log.app begin fun m -> m ~header:("Simplified") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
      hes) in
  (* let hes = Abbrev_variable_numbers.abbrev_variable_numbers_hes hes in *)
  let run =
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      FptProverRecLimitSolver.run
    ) else (
      match solve_options.solver with
      | Katsura -> KatsuraSolver.run
      | Iwayama -> IwayamaSolver.run
      | Suzuki  -> SuzukiSolver.run
    ) in
  run solve_options debug_context hes with_par >>| (fun s -> (s, debug_context))

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

let elim_mu_exists coe1 coe2 add_arguments coe_arguments no_elim lexico_pair_number _debug_output assign_values_for_exists_at_first_iteration (hes : 'a Hflz.hes) name =
  (* TODO: use 2nd return value of add_arguments *)
  let (arg_coe1, arg_coe2) = coe_arguments in
  if no_elim then begin
    let hes =
      if add_arguments
        then (let hes, _ = Manipulate.Add_arguments.add_arguments hes arg_coe1 arg_coe2 in hes)
        else hes in
    [hes, []]
  end else begin
    let hes, id_type_map =
      if add_arguments
        then Manipulate.Add_arguments.add_arguments hes arg_coe1 arg_coe2
        else hes, Hflmc2_syntax.IdMap.empty in
    let heses =
      if assign_values_for_exists_at_first_iteration && coe1 = 1 && coe2 = 1 then Manipulate.Hflz_manipulate_2.eliminate_exists_by_assinging coe1 hes
      else [Hflz_mani.encode_body_exists coe1 coe2 hes, []] in
    List.map (fun (hes, acc) ->
      Log.app begin fun m -> m ~header:("Exists-Encoded HES (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
      ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_exists_encoded.txt") hes;
      
      let hes = Hflz_mani.elim_mu_with_rec hes coe1 coe2 lexico_pair_number id_type_map in
      
      Log.app begin fun m -> m ~header:("Eliminate Mu (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
      if not @@ Hflz.ensure_no_mu_exists hes then failwith "elim_mu";
      ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_elim_mu.txt") hes;
      (* forall, nu *)
      hes, acc
    ) heses
  end

exception Exit

let summary_results (results : (Status.t * 'a) list) =
  let non_fail_results = List.filter (fun (r, _) -> match r with Status.Fail -> false | _ -> true) results in
  if (List.length @@ non_fail_results == 0)
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

(* これ以降、本プログラム側での近似が入る *)
let rec mu_elim_solver coe1 coe2 lexico_pair_number iter_count (solve_options : Solve_options.options) debug_output hes mode_name =
  Hflz_mani.simplify_bound := solve_options.simplify_bound;
  let nu_only_heses = elim_mu_exists coe1 coe2 solve_options.add_arguments solve_options.coe_arguments solve_options.no_elim lexico_pair_number debug_output solve_options.assign_values_for_exists_at_first_iteration hes mode_name in
  let debug_context_ = Some {
    mode = mode_name;
    iter_count = iter_count;
    coe1 = coe1;
    coe2 = coe2;
    pid = solve_options.pid;
    file = solve_options.file;
    solver_backend = None;
    default_lexicographic_order = lexico_pair_number;
    exists_assignment = None;
    temp_file = "";
  } in
  if not solve_options.dry_run then (
    (* e.g. solvers = [(* an instantiation of variables quantified by exists, e.g. x1 = 0 *)[solve with hoice, solve with z3]; (* x1 = 1*)[solve with hoice, solve with z3]]
      For each instantiation, if both hoice and z3 returned "fail," then the overall result is "fail."
      If either of hoice and z3 returned some result other than "fail," then the result of the current iteration is the result returned by the solvers.
      If one of instantiation of existential variables has returned "valid," then result of current iteration is "valid."
    *)
    let (solvers: (Status.t * debug_context option) Deferred.t list list) = 
      match solve_options.solver_backend with
      | None ->
        List.map (fun (nu_only_hes, exists_assignment) ->
          [
            solve_onlynu_onlyforall
              { solve_options with solver_backend = Some "hoice" }
              (Option.map (fun o -> { o with solver_backend = Some "hoice"; exists_assignment = Some exists_assignment }) debug_context_)
              nu_only_hes
              false;
            solve_onlynu_onlyforall
              { solve_options with solver_backend = Some "z3" }
              (Option.map (fun o -> { o with solver_backend = Some "z3"; exists_assignment = Some exists_assignment }) debug_context_)
              nu_only_hes
              false
          ]
        ) nu_only_heses
      | Some _ ->
        List.map (fun (nu_only_hes, _) -> [solve_onlynu_onlyforall solve_options debug_context_ nu_only_hes false]) nu_only_heses in
    let (is_valid : (Status.t * debug_context option list) list Ivar.t) = Ivar.create () in
    let deferred_is_valid = Ivar.read is_valid in
    let (deferred_all : (Status.t * debug_context option list) list Deferred.t) =
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
            let result, d = summary_results results in
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
    Deferred.any [deferred_is_valid; deferred_all]
    >>= (fun results -> kill_processes (Option.map (fun a -> a.mode) debug_context_)
    >>= (fun _ ->
        let result, debug_contexts = summary_results results in
        let debug_contexts = List.flatten debug_contexts in
        let retry coe1 coe2 =
          (* let (coe1',coe2',lexico_pair_number) =
            if (coe1,coe2,lexico_pair_number)=(1,1,1) then (1,1,2)
            else if (coe1,coe2,lexico_pair_number)=(1,1,2) then (1,8,1)
            else if lexico_pair_number=1 then (coe1,coe2,lexico_pair_number+1)
            else (2*coe1,2*coe2,1)
          in *)
          let (coe1',coe2',lexico_pair_number) =
            if (coe1,coe2,lexico_pair_number)=(1,1,1) && not solve_options.disable_lexicographic
            then (1,1,2)
            else if (coe1,coe2)=(1,1) 
              then (1,8,solve_options.default_lexicographic_order)
              else (2*coe1, 2*coe2,solve_options.default_lexicographic_order) in
          mu_elim_solver coe1' coe2' lexico_pair_number (iter_count + 1) solve_options false hes mode_name
        in
        match result with
        | Status.Valid -> return (Status.Valid, debug_contexts)
        | Status.Invalid -> retry coe1 coe2
        | Status.Unknown -> 
          if not solve_options.stop_on_unknown then (
            print_endline @@ "return Unknown (" ^ show_debug_contexts debug_contexts ^ ")";
            retry coe1 coe2
          ) else return (Status.Unknown, debug_contexts)
        | Status.Fail -> return (Status.Fail, debug_contexts)))
  ) else (print_endline "DRY RUN"; Deferred.return (Status.Unknown, [None]))

let check_validity_full coe1 coe2 (solve_options : Solve_options.options) hes cont =
  let hes_for_disprove = Hflz_mani.get_dual_hes hes in
  let dresult = Deferred.any
                  [mu_elim_solver coe1 coe2 solve_options.default_lexicographic_order 1 solve_options solve_options.print_for_debug hes "prover";
                   (mu_elim_solver coe1 coe2 solve_options.default_lexicographic_order 1 solve_options solve_options.print_for_debug hes_for_disprove "disprover" >>| (fun (s, i) -> Status.flip s, i))] in
  let dresult = dresult >>=
    (fun ri -> kill_processes (Some "prover") >>=
      (fun _ -> kill_processes (Some "disprover") >>|
        (fun _ -> ri))) in
  upon dresult (
    fun (result, info) ->
      cont (result, info);
      shutdown 0);
  Core.never_returns(Scheduler.go())

let solve_onlynu_onlyforall_with_schedule solve_options nu_only_hes cont =
  let dresult = Deferred.any [solve_onlynu_onlyforall { solve_options with no_disprove = false } None nu_only_hes true >>| (fun (s, _) -> s)] in
  upon dresult (fun result -> cont (result, [None]); Rfunprover.Solver.kill_z3(); shutdown 0);
  Core.never_returns(Scheduler.go())
  
(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity coe1 coe2 solve_options (hes : 'a Hflz.hes) cont =
  if solve_options.always_approximate then
    check_validity_full coe1 coe2 solve_options hes cont
  else begin
    if is_onlynu_onlyforall hes then
      solve_onlynu_onlyforall_with_schedule solve_options hes cont
    else if is_onlymu_onlyexists hes then
      solve_onlynu_onlyforall_with_schedule solve_options (Hflz_mani.get_dual_hes hes) (fun (status_pair, i) -> cont (Status.flip status_pair, i))
    else check_validity_full coe1 coe2 solve_options hes cont
  end

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
