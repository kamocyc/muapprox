module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status
module Solve_options = Solve_options
module Hflz_mani = Manipulate.Hflz_manipulate
module Hflz_convert = Hflz_convert
module Hflz_convert_rev = Hflz_convert_rev
module Check_formula_equality = Check_formula_equality

let read_strings file =
  let fp = open_in file in
  let rec loop() =
    try
      let s = input_line fp in (s::loop())
    with _ -> []
  in loop()
  
let get_status_from_z3_output result =
  match result with
  | [] -> failwith "no result"
  | "sat" :: _ -> Status.Valid
  | "unsat" :: _ -> Status.Invalid
  | "timeout" :: _ -> raise Status.Timeout
  | _ -> Status.Unknown
  
let read_command_outputs () =
  let unlines lines = String.concat "\n" lines in
  (read_strings "_stdout.txt" |> unlines, read_strings "_stderr.txt" |> unlines)

open Async
open Solve_options

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

type debug_context = {
  coe1: int;
  coe2: int;
  mode: string
}

let show_debug_context debug =
  match debug with
  | None -> ""
  | Some debug -> "(" ^ debug.mode ^ " / coe1=" ^ (string_of_int debug.coe1) ^ ", coe2=" ^ (string_of_int debug.coe2) ^ ")"

module type BackendSolver = sig
  (* val save_hes_to_file : Manipulate.Type.simple_ty Hflz.hes -> string
  
  val solver_command : string -> bool -> string array

  val parse_results : (unit, 'a) result * string * 'b -> Status.t *)
  
  val run : options -> debug_context option -> Hflmc2_syntax.Type.simple_ty Hflz.hes_rule list -> bool -> Status.t Deferred.t
end

(* TODO: 引用符で囲むなどの変換する？ *)
let unix_system commands =
  let commands = Array.concat [commands; [|">"; "_stdout.txt"; "2>"; "_stderr.txt"|]] in
  Unix.system ((String.concat " " (Array.to_list commands)))

module FptProverRecLimitSolver : BackendSolver = struct
  let convert_status (s : Fptprover.Status.t) : Status.t =
    match s with
    | Valid -> Valid
    | Invalid -> Invalid
    | Unknown -> Unknown
    | Sat -> Sat
    | UnSat -> UnSat
  
  let run option debug_context hes with_par =
    print_endline "FIRST-ORDER";
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes in
    print_endline @@ "HES PATH: " ^ path_;
    let hes = Hflz_convert_rev.of_hes hes in
    print_endline @@ "Converted Hes: " ^ Convert.Hesutil.str_of_hes hes;
    let hes' = Hflz_convert.of_hes hes in
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes' in
    print_endline @@ "HES PATH 2: " ^ path_;
    (* Global.config := Config.update_hoice true Global.config; *)
    (* 1, 2番目の引数は使われていない *)
    if with_par then
      Rfunprover.Solver.solve_onlynu_onlyforall_par false (int_of_float option.timeout) option.print_for_debug hes
        >>| (fun status -> convert_status status)
    else
      Rfunprover.Solver.solve_onlynu_onlyforall_z3 true (int_of_float option.timeout) option.print_for_debug hes 
        >>| (fun status -> convert_status status)
end

module KatsuraSolver : BackendSolver = struct
  let solver_path = "/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe"
  
  let save_hes_to_file hes debug_context =
    (* debug *)
    (* let hes = Hflmc2_syntax.Trans.Simplify.hflz_hes hes true in *)
    let path' = Manipulate.Print_syntax.MachineReadable.save_hes_to_file true hes in
    print_endline @@ "HES for backend " ^ (show_debug_context debug_context);
    print_endline path';
    
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file true hes
    
  let solver_command hes_path no_backend_inlining =
    if no_backend_inlining
    then [|solver_path; "--no-inlining"; hes_path;|]
    else [|solver_path; hes_path;|]

  let parse_results (exit_status, stdout, stderr) debug_context =
    match exit_status with 
    | Ok () -> begin
      (* Verification Result: の行を探す。 *)
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nProfiling:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        let status = Status.of_string @@ Str.matched_group 2 stdout in
        print_endline @@ "Parsed status: " ^ Status.string_of status ^ " " ^ (show_debug_context debug_context);
        status
      with
        | Not_found -> failwith @@ "not matched"
        | Invalid_argument s -> failwith @@ "Invalid_argument: " ^ s
      end
    | _ -> 
      (print_endline "error status"; Status.Unknown)
    
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let command = solver_command path solve_options.no_backend_inlining in
    unix_system command
    >>| (fun status_code ->
          try
            let stdout, stderr = read_command_outputs () in
            parse_results (status_code, stdout, stderr) debug_context
          with _ -> Status.Unknown)
        
    (* let status = parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:solve_options.timeout command in
    cont (status, status) *)
end

module IwayamaSolver : BackendSolver = struct
  let solver_path = "hflmc2"
  
  let save_hes_to_file hes debug_context =
    (* let hes = Hflmc2_syntax.Trans.Simplify.hflz_hes hes true in *)
    let path' = Manipulate.Print_syntax.MachineReadable.save_hes_to_file true hes in
    print_endline @@ "HES for backend " ^ (show_debug_context debug_context);
    print_endline path';
    
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file false hes
    
  let solver_command hes_path no_backend_inlining =
    if no_backend_inlining
    then [|solver_path; "--no-inlining"; hes_path;|]
    else [|solver_path; hes_path;|]

  let parse_results (exit_status, stdout, stderr) debug_context =
    match exit_status with 
    | Ok () -> begin
      (* Verification Result: の行を探す。 *)
      let regp = "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nLoop Count:$" in
      let reg = Str.regexp regp in
      try
        ignore @@ Str.search_forward reg stdout 0;
        let status = Status.of_string @@ Str.matched_group 2 stdout in
        print_endline @@ "PARSED STATUS: " ^ Status.string_of status ^ " " ^ (show_debug_context debug_context);
        status
      with
        | Not_found -> failwith @@ "not matched"
        | Invalid_argument s -> failwith @@ "Invalid_argument: " ^ s
      end
    | _ -> Status.Unknown
  
  let run solve_options debug_context hes _ = 
    let path = save_hes_to_file hes debug_context in
    let command = solver_command path solve_options.no_backend_inlining in
    unix_system command
    >>| (fun status_code ->
        try
          let stdout, stderr = read_command_outputs () in
          parse_results (status_code, stdout, stderr) debug_context
          with _ -> Status.Unknown)
    (* let status = parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:solve_options.timeout command in
    cont (status, status) *)
end

let rec is_first_order_function_type (ty : Hflmc2_syntax.Type.simple_ty) =
  match ty with
  | TyBool () -> true
  | TyArrow (ty1, ty2) -> 
    ty1.ty = TyInt && is_first_order_function_type ty2
  
let is_first_order_hes hes =
  Hflz_mani.decompose_lambdas_hes hes
  |> List.for_all (fun { Hflz.var; _} -> is_first_order_function_type var.ty)
  
let solve_onlynu_onlyforall solve_options debug_context hes with_par =
  let run =
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      FptProverRecLimitSolver.run
    ) else (
      match solve_options.solver with
      | Katsura -> KatsuraSolver.run
      | Iwayama -> IwayamaSolver.run
    ) in
  run solve_options debug_context hes with_par

(*     
  let (module Solver : BackendSolver) = (
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      (module FptProverRecLimitSolver)
    ) else (
      match solve_options.solver with
      | Katsura -> (module KatsuraSolver)
      | Iwayama -> (module IwayamaSolver)
    )) in
  let path = Solver.save_hes_to_file hes in
  let command = Solver.solver_command path solve_options.no_backend_inlining in
  let status = Solver.parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:solve_options.timeout command in
  status, status *)

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
let is_onlynu_onlyforall =
  List.for_all is_onlynu_onlyforall_rule

let is_onlyexists_body formula =
  fold_hflz (fun b f -> match f with Hflz.Forall _ -> false | _ -> b) formula true
let is_onlymu_onlyexists_rule {Hflz.var; fix; body} =
  (fix = Fixpoint.Least) && is_onlyexists_body body
let is_onlymu_onlyexists =
  List.for_all is_onlymu_onlyexists_rule

(* let flip_status_pair (s1, s2) =
  (Status.flip s1, s2) *)

(* TODO: forallを最外に移動？ => いらなそうか *)
let elim_mu_exists coe1 coe2 debug_output hes name =
  (* 再帰参照していない述語はgreatestに置換 *)
  (* これをすると、fixpoint alternationが新たにできて、式が複雑になることがあるので、やめる *)
  (* let hes = to_greatest_from_not_recursive rec_preds hes in *)
  (* forall, existential, nu, mu *)
  (* forall, nu, mu *)
  let hes = Hflz_mani.encode_body_exists coe1 coe2 hes in
  if debug_output then Log.app begin fun m -> m ~header:("Exists-Encoded HES (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
  if debug_output then ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_exists_encoded.txt") hes;
  let hes = Hflz_mani.elim_mu_with_rec hes coe1 coe2 in
  if debug_output then Log.app begin fun m -> m ~header:("Eliminate Mu (" ^ name ^ ")") "%a" Manipulate.Print_syntax.FptProverHes.hflz_hes' hes end;
  if not @@ Hflz.ensure_no_mu_exists hes then failwith "elim_mu";
  if debug_output then ignore @@ Manipulate.Print_syntax.FptProverHes.save_hes_to_file ~file:("muapprox_" ^ name ^ "_elim_mu.txt") hes;
  (* forall, nu *)
  hes

(* これ以降、本プログラム側での近似が入る *)
let rec mu_elim_solver coe1 coe2 solve_options debug_output hes mode_name = 
  let nu_only_hes = elim_mu_exists coe1 coe2 debug_output hes mode_name in
  let debug_context = Some {
    mode = mode_name;
    coe1 = coe1;
    coe2 = coe2;
  } in
  if not solve_options.dry_run then (
    (solve_onlynu_onlyforall solve_options debug_context nu_only_hes false)
    >>= (fun result ->
        match result with
      | Status.Valid -> return Status.Valid
      | Status.Invalid -> let (coe1',coe2') = if (coe1,coe2)=(1,1) then (1,8) else (2*coe1,2*coe2)
        in mu_elim_solver coe1' coe2' solve_options false hes mode_name                  
      | _ -> return Status.Unknown)
  ) else (print_endline "DRY RUN"; Unix.system "echo" >>| (fun _ -> Status.Unknown))
  (* solve_onlynu_onlyforall solve_options nu_only_hes (fun (result, result') -> 
    match result with
    | Status.Valid -> cont (Status.Valid, result')
    | _ -> begin
      let dual_hes = Hflz_mani.get_dual_hes hes in
      let nu_only_dual_hes = elim_mu_exists coe1 coe2 dual_hes in
      solve_onlynu_onlyforall solve_options nu_only_dual_hes (fun (dual_result, dual_result') -> 
        match dual_result with
        | Status.Valid -> cont (Status.Invalid, dual_result')
        | _ -> begin
          if solve_options.oneshot then
            cont (dual_result, dual_result')
          else
            (* koba-testの係数の増やし方を利用 *)
            let coe1, coe2 = if (coe1, coe2) = (1, 1) then (1, 8) else (2 * coe1, 2 * coe2) in
            go coe1 coe2
        end
      )
    end
  ) *)


(* let get_greatest_approx_hes hes =
  List.map (fun rule -> { rule with Hflz.fix = Fixpoint.Greatest }) hes 
   *)
let check_validity_full coe1 coe2 solve_options hes cont =
  let solvers = ref [] in
  (* if is_only_forall hes then ( (* forall + nu + mu *)
    let nu_relaxed_hes = get_greatest_approx_hes hes in
    Log.app begin fun m -> m ~header:"nu_relaxed_hes" "%a" Manipulate.Print_syntax.(MachineReadable.hflz_hes' simple_ty_ false) hes end;
    let nu_relax_solver = fun timeout is_print_for_debug ->
      let result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout is_print_for_debug nu_relaxed_hes in
      match result with
      | Status.Invalid -> Status.Invalid, Status.Invalid
      | status -> Status.Unknown, status
    in
    solvers := !solvers @ [nu_relax_solver, "nu-relaxed hes", true]
  ) *)
  let hes_for_disprove = Hflz_mani.get_dual_hes hes in
  let dresult = Deferred.any
                  [mu_elim_solver coe1 coe2 solve_options solve_options.print_for_debug hes "prover";
                   (mu_elim_solver coe1 coe2 solve_options solve_options.print_for_debug hes_for_disprove "disprover" >>| Status.flip)]
  in
  upon dresult (fun result -> cont result; Rfunprover.Solver.kill_z3();
                              (*kill_child(Unix.getpid());*) shutdown 0
                              );
  Core.never_returns(Scheduler.go())

let solve_onlynu_onlyforall_with_schedule solve_options nu_only_hes cont =
  let dresult = Deferred.any [solve_onlynu_onlyforall solve_options None nu_only_hes true] in
  upon dresult (fun result -> cont result; Rfunprover.Solver.kill_z3(); shutdown 0);
  Core.never_returns(Scheduler.go())
  
(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity coe1 coe2 solve_options hes cont =
  (* Log.app begin fun m -> m ~header:"check_validity (first)" "%a" Manipulate.Print_syntax.(MachineReadable.hflz_hes' simple_ty_ false) hes end; *)
  (* let hes = Hflz_mani.decompose_lambdas_hes hes in
  Log.app begin fun m -> m ~header:"Decompose lambdas" "%a" Manipulate.Print_syntax.(hflz_hes simple_ty_) hes end; *)
  (* let rec_preds = Manipulate.Hflz_util.get_recurring_predicates hes in *)
  (* print_endline "get_recurring_predicates";
    List.iter (fun p -> print_string @@ Hflmc2_syntax.Id.to_string p ^ ", ") rec_preds; print_endline ""; *)
  if is_onlynu_onlyforall hes then
    solve_onlynu_onlyforall_with_schedule solve_options hes cont
  else if is_onlymu_onlyexists hes then
    solve_onlynu_onlyforall_with_schedule solve_options (Hflz_mani.get_dual_hes hes) (fun status_pair -> cont @@ Status.flip status_pair)
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
