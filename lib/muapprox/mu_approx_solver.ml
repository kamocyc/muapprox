(* module Syntax = Hflmc2_syntax
module Mahflz = Hflmc2_syntax.Hflz
open Hflmc2_util
open Hflz_manipulate

let solver_path = "/opt/home2/git/hflmc2_mora/_build/default/bin/main.exe"
let solver_command hes_path = solver_path ^ " " ^ hes_path ^ " --no-inlining" 

let save_hes_to_file hes =
  Random.self_init ();
  let r = Random.int 0x10000000 in
  let file = Printf.sprintf "/tmp/%s-%d.smt2" "nuonly" r in
  let oc = open_out file in
  let fmt = Format.formatter_of_out_channel oc in
  Printf.fprintf oc "%%HES\n" ;
  Print_syntax.MachineReadable.hflz_hes' Syntax.Print.simple_ty_ fmt hes;
  Format.pp_print_flush fmt ();
  file

let parse_results msg =
  (* TODO: *)
  Status.Invalid
  
let run_solver timeout hes =
  let path = save_hes_to_file hes in
  let command = solver_command path in
  let status, std, err = Fn.run_command ~timeout:timeout [|command|] in
  (* TODO: 結果を取得 *)
  print_string "RESULTS:";
  print_string std;
  print_string err;
  let status = parse_results std in
  status, status
  
(* TODO: existentialがあると意味をなす *)
let rec is_onlyforall_ = function
  | Mahflz.Bool _ -> true
  | Mahflz.Var _  -> true
  | Mahflz.Or (f1, f2)  -> (is_onlyforall_ f1) && (is_onlyforall_ f2)
  | Mahflz.And (f1, f2) -> (is_onlyforall_ f1) && (is_onlyforall_ f2)
  | Mahflz.Abs (_, f1)  -> is_onlyforall_ f1
  | Mahflz.Forall (_, f1) -> is_onlyforall_ f1
  | Mahflz.Exists (_, f1) -> false
  | Mahflz.App (f1, f2)   -> (is_onlyforall_ f1) && (is_onlyforall_ f2)
  | Mahflz.Arith _  -> true
  | Mahflz.Pred _  -> true

module Hesutil = struct
  let is_onlyforall _ = true
  
  let get_greatest_approx_hes =
    List.map ~f:(fun rule -> { rule with Mahflz.fix = Greatest }) 
end

module Debug = struct
(* TODO *)
  let print s = print_string @@ s ^ "\n"
end

(* TODO: thunk *)
let solve_onlynu_onlyforall _ timeout is_print_for_debug hes =
  run_solver timeout hes
        
let get_mu_elimed_solver coe1 coe2 _ hes =
  let nu_only_hes = Hflz_convert.elim_mu_with_rec coe1 coe2 hes in
  solve_onlynu_onlyforall nu_only_hes
  
let flip_solver solver =
  fun timeout is_print_for_debug ->
  let status, original_status = solver timeout is_print_for_debug in
  Status.flip status, original_status
  

let rec run_solvers timeout is_print_chc = function
  | [] -> Status.Unknown
  | solvers ->
    let rec rep next_solvers = function
      | [] ->
        let next_timeout =
          timeout * 2
          (* if List.length next_solvers = 1 then 0 else timeout * 2 *)
        in
        run_solvers next_timeout false (List.rev next_solvers)
      | (solver, title, is_print) :: tail ->
        let is_print_chc = is_print_chc && is_print in
        if is_print_chc then
          (Debug.print "======================================";
           Debug.print ("CHC of " ^ title);
           Debug.print "======================================");
        if !Global.config.verbose then
          (Printf.printf "Solving %s %s..." title
           @@ if timeout = 0 then "without timeout" else Printf.sprintf "with timeout %d sec" timeout;
           if is_print_chc then
             Printf.printf "\n";
           flush stdout);
        try
          let status, original_status = solver timeout is_print_chc in
          if not is_print_chc && !Global.config.verbose then
            (Printf.printf " %s (<= %s)\n" (Status.string_of status) (Status.string_of original_status); flush stdout);
          if status = Status.Unknown then
            rep next_solvers tail
          else
            status
        with Status.Timeout ->
          if not is_print_chc && !Global.config.verbose then
            (Printf.printf " timeout\n"; flush stdout);
          rep ((solver, title, is_print) :: next_solvers) tail
    in
    rep [] solvers


(* TODO: existentialがあるとき *)
let solve_onlyforall (hes : Type.simple_ty Syntax.Hflz.hes) =
  (* TODO: free variableはfor allで処理するか、確認 *)
  (* let hes = Hesutil.elim_fv_with_forall hes in *)
  let solvers = ref [] in
  (* TODO: これが何をやっているのかわからない。 *)
  (* preconditionでforallonlyなのでは？elim_fv_with_forallで作られる？ *)
  (* leastをgreatestに置き換えるということか *)
  (* existenstion？ *)
  let hes = Hflz_convert.to_muapprox_hes hes in
  if Hesutil.is_onlyforall hes then (
    let nu_relaxed_hes = Hesutil.get_greatest_approx_hes hes in
    
    Debug.print "======================================";
    Debug.print "nu-relaxed hes";
    Debug.print "======================================";
    Hflz_convert.Print.hflz_hes Syntax.Print.simple_ty_ Format.std_formatter nu_relaxed_hes;
    Debug.print "";
    let nu_relax_solver = fun timeout is_print_for_debug ->
      let result, _ = solve_onlynu_onlyforall false timeout is_print_for_debug nu_relaxed_hes in
      match result with
      | Status.Invalid -> Status.Invalid, Status.Invalid
      | status -> Status.Unknown, status
    in
    solvers := !solvers @ [nu_relax_solver, "nu-relaxed hes", true]
  );
  let coe1, coe2 = 1, 1 in
  let hes_for_disprove = Hflz_manipulate.get_dual_hes hes in
  Debug.print "======================================";
  Debug.print "Generating mu-eliminated hes";
  Debug.print "======================================";
  ignore @@ get_mu_elimed_solver coe1 coe2 true hes;
  Debug.print "======================================";
  Debug.print "Generating hes for disproving";
  Debug.print "======================================";
  ignore @@ flip_solver @@ get_mu_elimed_solver coe1 coe2 true hes_for_disprove;
  solvers := !solvers @ [
      (get_mu_elimed_solver coe1 coe2 false hes, Printf.sprintf "mu-eliminated hes with coe=%d,%d" coe1 coe2, true);
      (flip_solver @@ get_mu_elimed_solver coe1 coe2 false hes_for_disprove, Printf.sprintf "hes for disproving with coe=%d,%d" coe1 coe2, true);
    ];
  if config.coe = None then
    solvers := !solvers @ [
        (get_mu_elimed_solver 1 2 false hes,  "mu-eliminated hes with coe=1,2", false);
        (flip_solver @@ get_mu_elimed_solver 1 2 false hes_for_disprove,  "hes for disproving with coe=1,2", false);
        (get_mu_elimed_solver 1 10 false hes,  "mu-eliminated hes with coe=1,10", false);
        (flip_solver @@ get_mu_elimed_solver 1 10 false hes_for_disprove,  "hes for disproving with coe=1,10", false);
      ];
  run_solvers 1 true !solvers *)