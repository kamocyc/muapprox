module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status
module Solve_options = Solve_options
module Hflz_mani = Manipulate.Hflz_manipulate
module Hflz_convert = Hflz_convert
module Hflz_convert_rev = Hflz_convert_rev

open Solve_options

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

module type BackendSolver = sig
  (* val save_hes_to_file : Manipulate.Type.simple_ty Hflz.hes -> string
  
  val solver_command : string -> bool -> string array

  val parse_results : (unit, 'a) result * string * 'b -> Status.t *)
  
  val run : options -> Hflmc2_syntax.Type.simple_ty Hflz.hes_rule list -> Status.t * Status.t
end

module FptProverRecLimitSolver : BackendSolver = struct
  (* let solver_path = "/opt/home2/git/fptprove_muarith/_build/default/bin/main.exe"
  
  let save_hes_to_file hes =
    match hes with 
    | [] -> failwith "save_hes_to_file"
    | first_rule::rem_rules -> 
    (* check *)
      let rec_preds = Hflz_util.get_recurring_predicates hes in
      if List.exists (fun id -> id = first_rule.var ) rec_preds then failwith "hflz_hes': First rule is recursive";
      if first_rule.var.ty <> TyBool () then failwith "hflz_hes': First rule has arguments";
      Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes
  
  (* TODO *)
  let solver_command hes_path no_backend_inlining =
    let common = [|solver_path; "--algorithm"; "rec-limit"; "--format"; "hes"; "-e"; "nu"|] in
    if no_backend_inlining
    then Array.concat [common; [|"--no-inlining"; hes_path|]]
    else Array.concat [common; [|hes_path;|]]

  let parse_results (exit_status, stdout, stderr) =
    match exit_status with 
    | Ok () -> begin
      let status_string = String.split_on_char '\n' stdout |> List.rev |> List.hd in
      try
        let status = Status.of_string status_string in
        print_endline @@ "PARSED STATUS: " ^ Status.string_of status;
        status
      with
        | Invalid_argument s -> failwith @@ "Invalid_argument: " ^ s
      end
    | _ -> Status.Unknown
   *)
   
  let convert_status (s : Fptprover.Status.t) : Status.t =
    match s with
    | Valid -> Valid
    | Invalid -> Invalid
    | Unknown -> Unknown
    | Sat -> Sat
    | UnSat -> UnSat
  
  let run options hes =
    print_endline "FIRST-ORDER";
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes in
    print_endline @@ "HES PATH: " ^ path_;
    let hes = Hflz_convert_rev.of_hes hes in
    print_endline @@ "Converted Hes: " ^ Convert.Hesutil.str_of_hes hes;
    let hes' = Hflz_convert.of_hes hes in
    let path_ = Manipulate.Print_syntax.FptProverHes.save_hes_to_file hes' in
    print_endline @@ "HES PATH 2: " ^ path_;
    let status, _ = Rfunprover.Solver.solve_onlynu_onlyforall false (int_of_float options.timeout) options.print_for_debug hes in
    let status = convert_status status in
    status, status
    (* failwith "a" *)
end

module KatsuraSolver : BackendSolver = struct
  let solver_path = "/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe"
  
  let save_hes_to_file hes =
    (* debug *)
    let psi = Hflmc2_syntax.Trans.Simplify.hflz_hes hes true in
    let path' = Manipulate.Print_syntax.MachineReadable.save_hes_to_file true psi in
    print_endline "converted and simplified";
    print_endline path';
    
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file true hes
    
  let solver_command hes_path no_backend_inlining =
    if no_backend_inlining
    then [|solver_path; "--no-inlining"; hes_path;|]
    else [|solver_path; hes_path;|]

  let parse_results (exit_status, stdout, stderr) =
    match exit_status with 
    | Ok () -> begin
      (* Verification Result: の行を探す。 *)
      let reg = Str.regexp "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nProfiling:$" in
      try
        ignore @@ Str.search_forward reg stdout 0;
        let status = Status.of_string @@ Str.matched_group 2 stdout in
        print_endline @@ "PARSED STATUS: " ^ Status.string_of status;
        status
      with
        | Not_found -> failwith @@ "not matched"
        | Invalid_argument s -> failwith @@ "Invalid_argument: " ^ s
      end
    | _ -> Status.Unknown
    
  let run solve_options hes = 
    let path = save_hes_to_file hes in
    let command = solver_command path solve_options.no_backend_inlining in
    let status = parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:solve_options.timeout command in
    status, status
end

module IwayamaSolver : BackendSolver = struct
  let solver_path = "hflmc2"
  
  let save_hes_to_file hes =    
    let psi = Hflmc2_syntax.Trans.Simplify.hflz_hes hes true in
    let path' = Manipulate.Print_syntax.MachineReadable.save_hes_to_file true psi in
    print_endline "converted and simplified";
    print_endline path';
    
    Manipulate.Print_syntax.MachineReadable.save_hes_to_file false hes
    
  let solver_command hes_path no_backend_inlining =
    if no_backend_inlining
    then [|solver_path; "--no-inlining"; hes_path;|]
    else [|solver_path; hes_path;|]

  let parse_results (exit_status, stdout, stderr) =
    match exit_status with 
    | Ok () -> begin
      (* Verification Result: の行を探す。 *)
      let regp = "^Verification Result:\n\\( \\)*\\([a-zA-Z]+\\)\nLoop Count:$" in
      let reg = Str.regexp regp in
      try
        ignore @@ Str.search_forward reg stdout 0;
        let status = Status.of_string @@ Str.matched_group 2 stdout in
        print_endline @@ "PARSED STATUS: " ^ Status.string_of status;
        status
      with
        | Not_found -> failwith @@ "not matched"
        | Invalid_argument s -> failwith @@ "Invalid_argument: " ^ s
      end
    | _ -> Status.Unknown
  
  let run solve_options hes = 
    let path = save_hes_to_file hes in
    let command = solver_command path solve_options.no_backend_inlining in
    let status = parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:solve_options.timeout command in
    status, status
end

let rec is_first_order_function_type (ty : Hflmc2_syntax.Type.simple_ty) =
  match ty with
  | TyBool () -> true
  | TyArrow (ty1, ty2) -> 
    ty1.ty = TyInt && is_first_order_function_type ty2
  
let is_first_order_hes hes =
  Hflz_mani.decompose_lambdas_hes hes
  |> List.for_all (fun { Hflz.var; _} -> is_first_order_function_type var.ty)
  
let run_solver solve_options hes =
  let run =
    if is_first_order_hes hes && solve_options.first_order_solver = Some FptProverRecLimit then (
      FptProverRecLimitSolver.run
    ) else (
      match solve_options.solver with
      | Katsura -> KatsuraSolver.run
      | Iwayama -> IwayamaSolver.run
    ) in
  run solve_options hes
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
   
let solve_onlynu_onlyforall solve_options rec_preds hes =
  run_solver solve_options hes

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
let is_onlynu_onlyforall_rule rec_preds {Hflz.var; fix; body} =
  (fix = Fixpoint.Greatest (*|| is_not_recursive rec_preds var*)) && is_onlyforall_body body
let is_onlynu_onlyforall rec_preds =
  List.for_all (is_onlynu_onlyforall_rule rec_preds)

let is_onlyexists_body formula =
  fold_hflz (fun b f -> match f with Hflz.Forall _ -> false | _ -> b) formula true
let is_onlymu_onlyexists_rule rec_preds {Hflz.var; fix; body} =
  (fix = Fixpoint.Least (*|| is_not_recursive rec_preds var*)) && is_onlyexists_body body
let is_onlymu_onlyexists rec_preds =
  List.for_all (is_onlymu_onlyexists_rule rec_preds)

let flip_status_pair (s1, s2) =
  (Status.flip s1, s2)

(* TODO: forallを最外に移動？ => いらなそうか *)
let elim_mu_exists coe1 coe2 rec_preds hes =
  (* 再帰参照していない述語はgreatestに置換 *)
  (* これをすると、fixpoint alternationが新たにできて、式が複雑になることがあるので、やめる *)
  (* let hes = to_greatest_from_not_recursive rec_preds hes in *)
  (* forall, existential, nu, mu *)
  (* forall, nu, mu *)
  let hes = Hflz_mani.encode_body_exists coe1 coe2 hes in
  let hes = Hflz_mani.elim_mu_with_rec hes coe1 coe2 in
  if not @@ Hflz.ensure_no_mu_exists hes then failwith "elim_mu_exists";
  (* forall, nu *)
  hes
  
(* これ以降、本プログラム側での近似が入る *)
let check_validity_full coe1 coe2 solve_options rec_preds hes = 
  let rec go coe1 coe2 =
    (*  *)
    let nu_only_hes = elim_mu_exists coe1 coe2 rec_preds hes in
    let result, result' = solve_onlynu_onlyforall solve_options rec_preds nu_only_hes in
    match result with
    | Status.Valid -> (Status.Valid, result')
    | _ -> begin
      let dual_hes = Hflz_mani.get_dual_hes hes in
      let nu_only_dual_hes = elim_mu_exists coe1 coe2 rec_preds dual_hes in
      let dual_result, dual_result' = solve_onlynu_onlyforall solve_options rec_preds nu_only_dual_hes in
      match dual_result with
      | Status.Valid -> (Status.Invalid, dual_result')
      | _ -> begin
        if solve_options.oneshot then
          (dual_result, dual_result')
        else
          (* koba-testの係数の増やし方を利用 *)
          let coe1, coe2 = if (coe1, coe2) = (1, 1) then (1, 8) else (2 * coe1, 2 * coe2) in
          go coe1 coe2
      end
    end
  in
  go coe1 coe2

(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity coe1 coe2 solve_options hes =
  Log.app begin fun m -> m ~header:"check_validity (first)" "%a" Manipulate.Print_syntax.(MachineReadable.hflz_hes' simple_ty_ false) hes end;
  let hes = Hflz_mani.decompose_lambdas_hes hes in
  Log.app begin fun m -> m ~header:"Decompose lambdas" "%a" Manipulate.Print_syntax.(hflz_hes simple_ty_) hes end;
  let rec_preds = Manipulate.Hflz_util.get_recurring_predicates hes in
  print_endline "get_recurring_predicates";
    List.iter (fun p -> print_string @@ Hflmc2_syntax.Id.to_string p ^ ", ") rec_preds; print_endline "";
  if is_onlynu_onlyforall rec_preds hes then
    solve_onlynu_onlyforall solve_options rec_preds hes
  else if is_onlymu_onlyexists rec_preds hes then
    flip_status_pair @@ solve_onlynu_onlyforall solve_options rec_preds @@ Hflz_mani.get_dual_hes hes
  else check_validity_full coe1 coe2 solve_options rec_preds hes

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