module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
module Status = Status

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

let solver_path = "/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe"
let solver_command hes_path = [|solver_path; hes_path;|]

let save_hes_to_file hes =
  Random.self_init ();
  let r = Random.int 0x10000000 in
  let file = Printf.sprintf "/tmp/%s-%d.smt2" "nuonly" r in
  let oc = open_out file in
  let fmt = Format.formatter_of_out_channel oc in
  Printf.fprintf oc "%%HES\n" ;
  Print_syntax.MachineReadable.hflz_hes' Hflmc2_syntax.Print.simple_ty_ fmt hes;
  Format.pp_print_flush fmt ();
  close_out oc;
  file

(* TODO: timetoutのとき？ *)
let parse_results_ (exit_status, stdout, stderr) =
  match exit_status with 
  | Unix.WEXITED c when c = 0 -> begin
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
  
let run_solver timeout hes =
  let path = save_hes_to_file hes in
  let command = solver_command path in
  let status = parse_results @@ Hflmc2_util.Fn.Command.run_command ~timeout:timeout command in
  status, status
  
let solve_onlynu_onlyforall _ timeout is_print_for_debug rec_preds hes =
  let hes =
    List.map
      (fun ({Hflz.var; _} as rule) ->
        if not @@ List.exists (Hflmc2_syntax.Id.eq var) rec_preds
        then { rule with fix = Fixpoint.Greatest}
        else rule)
      hes in
  run_solver timeout hes
        
let get_mu_elimed_solver coe1 coe2 _ hes =
  let nu_only_hes = Hflz_manipulate.elim_mu_with_rec coe1 coe2 hes in
  solve_onlynu_onlyforall nu_only_hes
  
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

let is_not_recursive rec_preds var = not @@ List.exists (Hflmc2_syntax.Id.eq var) rec_preds
let to_greatest_from_not_recursive rec_preds =
  List.map
    (fun ({Hflz.var; _} as rule) ->
      if is_not_recursive rec_preds var
      then { rule with fix = Fixpoint.Greatest}
      else rule)

let is_onlyforall_body formula =
  fold_hflz (fun b f -> match f with Hflz.Exists _ -> false | _ -> b) formula true
let is_onlynu_onlyforall_rule rec_preds {Hflz.var; fix; body} =
  (fix = Fixpoint.Greatest || is_not_recursive rec_preds var) && is_onlyforall_body body
let is_onlynu_onlyforall rec_preds =
  List.for_all (is_onlynu_onlyforall_rule rec_preds)

let is_onlyexists_body formula =
  fold_hflz (fun b f -> match f with Hflz.Forall _ -> false | _ -> b) formula true
let is_onlymu_onlyexists_rule rec_preds {Hflz.var; fix; body} =
  (fix = Fixpoint.Least || is_not_recursive rec_preds var) && is_onlyexists_body body
let is_onlymu_onlyexists rec_preds =
  List.for_all (is_onlymu_onlyexists_rule rec_preds)

let flip_status_pair (s1, s2) =
  (Status.flip s1, s2)

(* TODO: forallを最外に移動？ => いらなそうか *)
let elim_mu_exists coe1 coe2 rec_preds hes =
  let hes = to_greatest_from_not_recursive rec_preds hes in
  (* forall, existential, nu, mu *)
  let hes = Hflz_manipulate.encode_body_exists coe1 coe2 hes in
  (* forall, nu, mu *)
  let hes = Hflz_manipulate.elim_mu_with_rec coe1 coe2 hes in 
  (* forall, nu *)
  hes
  
(* これ以降、本プログラム側での近似が入る *)
let check_validity_full coe1 coe2 _ timeout (is_print_for_debug : bool) (oneshot : bool) rec_preds hes = 
  let dual_hes = Hflz_manipulate.get_dual_hes hes in
  Log.app begin fun m -> m ~header:"dual_hes" "%a"
    Print_syntax.(hflz_hes simple_ty_) dual_hes
  end;
  let rec go coe1 coe2 =
    (*  *)
    let nu_only_hes = elim_mu_exists coe1 coe2 rec_preds hes in
    let result, result' = solve_onlynu_onlyforall () timeout is_print_for_debug rec_preds nu_only_hes in
    match result with
    | Status.Valid -> (Status.Valid, result')
    | _ -> begin
      let nu_only_dual_hes = elim_mu_exists coe1 coe2 rec_preds dual_hes in
      let dual_result, dual_result' = solve_onlynu_onlyforall () timeout is_print_for_debug rec_preds nu_only_dual_hes in
      match dual_result with
      | Status.Valid -> (Status.Invalid, dual_result')
      | _ -> begin
        if oneshot then
          (dual_result, dual_result')
        else
          (* TODO: 係数の増やし方 *)
          (* TODO: 再帰回数の制限？timeout？ *)
          go (coe1 * 2) (coe2 * 2)
      end
    end
  in
  go coe1 coe2
    
(* 「shadowingが無い」とする。 *)
(* timeoutは個別のsolverのtimeout *)  
let check_validity coe1 coe2 _ timeout (is_print_for_debug : bool) (oneshot : bool) hes =
  let hes = Hflz_manipulate.decompose_lambdas_hes hes in
  Log.app begin fun m -> m ~header:"Decompose lambdas" "%a"
    Print_syntax.(hflz_hes simple_ty_) hes
  end;
  let rec_preds = Hflz_a.get_recurring_predicates hes in
  print_endline "get_recurring_predicates";
    List.iter (fun p -> print_string @@ Hflmc2_syntax.Id.to_string p ^ ", ") rec_preds; print_endline "";
  if is_onlynu_onlyforall rec_preds hes then
    solve_onlynu_onlyforall () timeout is_print_for_debug rec_preds hes
  else if is_onlymu_onlyexists rec_preds hes then
    flip_status_pair @@ solve_onlynu_onlyforall () timeout is_print_for_debug rec_preds @@ Hflz_manipulate.get_dual_hes hes
  else check_validity_full coe1 coe2 () timeout is_print_for_debug oneshot rec_preds hes

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