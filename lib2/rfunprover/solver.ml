open Z3
open Smt
open Ast
open Ast.Logic
open Fptprover
open Convert
open Hes

(* ... (query!0 10 (- 2))))) -> [1001, -2] *)
(* let get_example (answer: Expr.expr) =
   let answer_str = Expr.to_string answer in
   let reg = Str.regexp "query!0 \\(\\( ?[0-9]+\\| ?(- [0-9]+)\\)*\\))*$" in
   let _ = Str.search_forward reg answer_str 0 in
   let args = String.split_on_char ' '
    @@ Str.global_replace
      (Str.regexp "(- \\([0-9]+\\))") "-\\1"
    @@ Str.matched_group 1 answer_str in
   List.map (fun arg_str ->
      int_of_string arg_str
    ) args *)
(* 
module CU = struct  
  open Core
  type t_result = (unit, [ `Exit_non_zero of int | `Signal of Signal.t | `Timeout]) result
  
  let output_lines (output : string list) (chan : Out_channel.t) : unit =
    List.iter
      ~f:(fun line -> Out_channel.output_string chan (line ^ "\n"))
      output;
    Out_channel.flush chan

  let rec do_channel_lines (f : string -> 'a) (chan : In_channel.t) (read_line_handler : string -> unit) : 'a list =
    match In_channel.input_line chan with
    | None -> []
    | Some line -> begin
      read_line_handler line;
      f line :: do_channel_lines f chan read_line_handler
    end
  let input_lines = do_channel_lines (fun x -> x)

  let unlines : string list -> string = String.concat ~sep:"\n"

  
  let async_command (timeout : float) (name : string) (arguments : string list) :
    Unix.Process_channels.t =
    (* use sigkill ? *)
    Unix.open_process_full
      (Printf.sprintf "bash -c 'timeout %s %s %s'"
        (string_of_float timeout)
        name
        (String.concat ~sep:" " arguments))
      ~env:(Unix.environment ())

  let pp_process_result fmt status out err =
    let show_status status = match status with
    | Ok _ -> "Ok"
    | Error (`Exit_non_zero 124) -> "Timeout"
    | Error (`Exit_non_zero c) -> "Error (`Exit_non_zero " ^ string_of_int c ^ ")"
    | Error (`Signal _) -> "Error (`Signal )" in
    Format.pp_print_string fmt @@ "Process result:\n";
    Format.pp_print_string fmt @@ "out: " ^ out ^ "\n";
    Format.pp_print_string fmt @@ "status: " ^ (show_status status) ^ "\n";
    Format.pp_print_string fmt @@ "err:\n" ^ err ^ "\n\n"

  let sync_command_full (timeout : float) (name : string) (arguments : string list)
      (input : string list) (read_line_handler : string -> unit) (read_err_line_handler : string -> unit) : t_result * string * string =
    let pcs = async_command timeout name arguments in
    output_lines input pcs.stdin;
    let out = unlines @@ input_lines pcs.stdout read_line_handler in
    let err = unlines @@ input_lines pcs.stderr read_err_line_handler in
    let status = Unix.close_process_full pcs in
    pp_process_result Format.std_formatter status out err;
    match status with
    | Ok () -> (Ok (), out, err)
    | Error (`Exit_non_zero 124) -> (Error (`Timeout), out, err)
    | Error (`Exit_non_zero c) -> (Error (`Exit_non_zero c), out, err)
    | Error (`Signal x) ->
      if Signal.equal x Signal.int then raise Sys.Break else (Error (`Signal x), out, err)
  
  let sync_command timeout name arguments input = sync_command_full timeout name arguments input print_endline (fun _ -> ())
  
  let run_command ?(timeout=10.0) commands =
    Format.pp_print_string Format.std_formatter @@ "Run command (muapprox) \"" ^ (String.concat ~sep:" " @@ Array.to_list commands) ^ "\"\n";
    match Array.to_list commands with
    | [] -> failwith "run_command"
    | name::arguments -> sync_command timeout name arguments []
end *)

let rec get_status_from_hoice_output result =
  match result with
  | [] -> failwith "no result"
  | "sat" :: _ -> Status.Valid
  | "unsat" :: _ -> Status.Invalid
  | "timeout" :: _ -> raise Status.Timeout
  | msg :: tail ->
    if Str.string_match (Str.regexp "^(error \\\"$") msg 0 then
      let rec read_error errors = function
        | [] -> failwith @@ Printf.sprintf "can't read error from %s" @@ String.concat "\n" result
        | "\")" :: tail -> errors, tail
        | error :: tail -> read_error (error :: errors) tail
      in
      let errors, tail = read_error [] tail in
      try let _ = get_status_from_hoice_output tail in
        raise @@ Status.Error (String.concat "\n" errors)
      with Status.Error error ->
        raise @@ Status.Error ((String.concat "\n" errors) ^ "\n\n" ^ error)
    else if Str.string_match (Str.regexp "^; |===| Warning:") msg 0 then
      let rec read_warning = function
        | [] -> failwith @@ Printf.sprintf "can't read warning from %s" @@ String.concat "\n" result
        | "; |===|" :: tail -> tail
        | _ :: tail -> read_warning tail
      in
      let tail = read_warning tail in
      get_status_from_hoice_output tail
    else
      failwith @@ Printf.sprintf "unknown result: %s" msg;;

let get_status_from_z3_output result =
  match result with
  | [] -> failwith "no result"
  | "sat" :: _ -> Status.Valid
  | "unsat" :: _ -> Status.Invalid
  | "timeout" :: _ -> raise Status.Timeout
  | _ -> Status.Unknown
       
let hoice solver ctx entry_funname entry_bounds is_need_example timeout is_print_for_debug =
  (* set params *)
  let params = Params.mk_params ctx in
  Params.add_bool params (Symbol.mk_string ctx "print_fixedpoint_extensions") false;
  Z3.Fixedpoint.set_parameters solver params;
  (* make (assert (forall ((A Int)) (not (Entry_ A)))) *)
  (* (forall () entry_app) if bounds = [] *)
  let arg_names = List.mapi (fun idx _ -> "X" ^ (string_of_int idx)) entry_bounds in
  let entry_assert_str =
    Printf.sprintf "(assert (forall (%s) (not (%s))))"
      (String.concat " "
       @@ List.map (fun (var_name, (_, sort)) ->
           Printf.sprintf "(%s %s)" var_name (Z3.Sort.to_string @@ Z3interface.of_sort ctx sort))
       @@ Core.List.zip_exn arg_names entry_bounds)
      (String.concat " "
       @@ entry_funname :: arg_names)
  in
  (* make smt string *)
  let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
  let reg_forall = Str.regexp "^(forall " in
  let prefix = ref "" in
  let inputs =
    List.map
      (fun line ->
         if Str.string_match reg_assert line 0 then
           let matched_str = Str.matched_group 1 line in
           let line' = !prefix in
           line'
           ^
           if not @@ Str.string_match reg_forall matched_str 0 then (
             prefix := ")\n";
             "(assert (forall () " ^ matched_str
           )
           else (
             prefix := "";
             line
           )
         else
           line
      )
    @@ String.split_on_char '\n'
    @@ Fixedpoint.to_string solver
  in
  let inputs = inputs @ [
      !prefix;
      entry_assert_str;
      "(check-sat)";
    ]
  in
  let inputs = if is_need_example then
      "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
    else
      inputs
  in
  let inputs = inputs @ ["(exit)"] in
  if !Global.config.verbose && is_print_for_debug then
    (Debug.print @@ Printf.sprintf "Horn Clause (hoice):";
     Debug.print @@ Printf.sprintf "%s" @@ String.concat "\n" inputs;
     flush stderr);
  let args = if timeout = 0 then [] else ["--timeout"; string_of_int timeout] in
  Util.Command.sync_command "hoice" args inputs


let solve_with_z3 solver entry_fun is_print_for_debug =
  try let z3result = Fixedpoint.query_r solver [entry_fun] in
    if is_print_for_debug then
      (Debug.print @@ Printf.sprintf "Z3: %s" (Solver.string_of_status z3result);
       Debug.print @@ "");
    match z3result with
    | Solver.SATISFIABLE -> (Status.Valid, None)
    | Solver.UNSATISFIABLE -> (Status.Invalid, None)
    | Solver.UNKNOWN -> (Status.Unknown, None)
  with
  | Z3.Error reason ->
    if is_print_for_debug then
      (Debug.print @@ Printf.sprintf "Z3: %s" reason;
       Debug.print @@ "");
    (* timeout *)
    if reason = "spacer canceled" || reason = "canceled" then
      raise Status.Timeout
    else
      (Debug.print @@ Printf.sprintf "Z3 Error: %s" reason;
       flush stderr;
       (Status.Unknown, None))

let solve_onlymu_onlyexists is_need_example timeout is_print_for_debug hes =
  assert (Hesutil.is_onlyexists hes);
  assert (HesLogic.is_onlymu hes);
  let hes = Hesutil.move_quantifiers_to_front hes in
  let options = if timeout = 0 then [] else ["timeout", string_of_int @@ timeout * 1000] in
  let ctx = mk_context options in
  let funcs = HesLogic.get_functions hes in
  (* make environment for functions *)
  let penv = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let symbol = match pvar with Ident.Pvar name ->
        Z3.Symbol.mk_string ctx name
      in
      let args = HesLogic.get_args_of_function func in
      let arg_sorts = List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) args in
      let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
      (pvar, func_decl)
    ) funcs
  in
  (* make derivations from functions *)
  let derivations = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let args = HesLogic.get_args_of_function func in
      let body = HesLogic.get_body_of_function func in
      let env = List.rev args in
      Z3interface.of_formula ctx env penv
      @@ Formula.mk_imply
        body
        (Formula.mk_atom
           (Atom.mk_app
              (Predicate.mk_var pvar
                 (List.map (fun (_, sort) -> sort) args))
              (List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) args)
              Dummy)
           Dummy)
        Dummy
    ) funcs in
  (* make a derivation and a rel from the entry point *)
  let entry = HesLogic.get_entrypoint hes in
  let bounds, entry =
    if Formula.is_exists entry then
      let bounds, body, _ = Formula.let_exists entry in
      bounds, body
    else
      [], entry
  in
  let entry_funname = "Entry_" in
  let entry_fun = FuncDecl.mk_func_decl ctx
      (Symbol.mk_string ctx entry_funname)
      (List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) bounds)
      (Boolean.mk_sort ctx)
  in
  let env = List.rev bounds in
  let entry = Z3interface.of_formula ctx env penv entry in
  let entry_app =
    (Z3.Expr.mk_app ctx entry_fun
       (List.rev
          (List.mapi
             (fun i (_, sort) ->
                Quantifier.mk_bound ctx i (Z3interface.of_sort ctx sort)) (List.rev bounds))))
  in
  let derivations =
    (Z3.Boolean.mk_implies ctx entry entry_app)
    :: derivations
  in
  (* make solver *)
  let solver = Fixedpoint.mk_fixedpoint ctx in
  (* register functions (or relations) *)
  List.iter (fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
  Z3.Fixedpoint.register_relation solver entry_fun;
  (* register derivations *)
  List.iter (fun c -> Z3.Fixedpoint.add_rule solver c None) derivations;
  (* query *)
  if is_need_example then
    let result = hoice solver ctx entry_funname bounds true timeout is_print_for_debug in
    if is_print_for_debug then
      Debug.print @@ Printf.sprintf "Hoice: %s\n" (String.concat "\n" result);
    let status = get_status_from_hoice_output result in
    (Status.flip status, None) (* TODO: get example *)
  else
    (* use hoice first *)
    try
      let result = hoice solver ctx entry_funname bounds false timeout is_print_for_debug in
      if is_print_for_debug then
        Debug.print @@ Printf.sprintf "Hoice: %s" (String.concat "\n" result);
      (Status.flip @@ get_status_from_hoice_output result, None)
    with
      Status.Timeout ->
      (* use z3 *)
      (* let config = !Global.config in
         if config.verbose then
         (Debug.print @@ Printf.sprintf "Horn Clause (z3):";
         Debug.print @@ Printf.sprintf "%s" @@ Z3.Fixedpoint.to_string solver;
         Debug.print @@ Printf.sprintf "(query Entry_)";
         Debug.print @@ Printf.sprintf "(exit)";
         flush stderr); *)
      solve_with_z3 solver entry_fun is_print_for_debug
    | Util.Command.Shell_error error ->
      if is_print_for_debug then
        Debug.print @@ Printf.sprintf "Shell Error in hoice: %s\n" error;
      solve_with_z3 solver entry_fun is_print_for_debug

let solve_onlynu_onlyforall is_need_example timeout is_print_for_debug hes =
  let result, ce = solve_onlymu_onlyexists is_need_example timeout is_print_for_debug @@ Hesutil.get_dual_hes hes in
  (Status.flip result, ce)

let solve_nobounds _ =
  (* let entry = (HesLogic.get_entrypoint hes) in
     let funcs = HesLogic.Utils.elim_mu_from_funcs_with_rec (HesLogic.get_functions hes) in *)
  Printf.printf "not implemented";
  assert false (* TODO *)

(* let solve_onlymu_onlyforall hes is_need_example = *)

let solve_general _ =
  Printf.printf "not implemented";
  assert false (* TODO *)

let solve is_need_example is_print_for_debug hes =
  let timeout = 0 in
  if Hesutil.is_onlyexists hes && HesLogic.is_onlymu hes then
    solve_onlymu_onlyexists is_need_example timeout is_print_for_debug hes
  else if Hesutil.is_onlyforall hes && HesLogic.is_onlynu hes then
    solve_onlynu_onlyforall is_need_example timeout is_print_for_debug hes
    (* else if HesLogic.is_onlyforall hes && HesLogic.is_onlymu hes then
       solve_onlymu_onlyforall hes is_need_example *)
  else if Hesutil.is_noquantifier hes then
    (solve_nobounds hes, Some [])
  else
    solve_general hes

let solve_formula fml =
  Debug.print @@ Printf.sprintf "Input Formula: %s" @@ PrinterHum.str_of_formula fml;
  let fml = Formula.simplify @@ FormulaConverter.elim_fv_with_forall fml in
  Debug.print @@ Printf.sprintf "Input Formula: %s" @@ PrinterHum.str_of_formula fml;
  let hes = Hesutil.move_quantifiers_to_front @@ Hesutil.hes_of_formula fml in
  Debug.print @@ Printf.sprintf "Input Hes: %s" @@ Hesutil.str_of_hes hes;
  let status, _ = solve false true hes in
  status

let fileid = ref 0;;
let get_fileid() = (fileid := !fileid+1; !fileid);;

let write_strings strings file =
  let fp = open_out file in
  List.iter (fun s -> (output_string fp (s^"\n"))) strings; close_out fp;;

let read_strings file =
  let fp = open_in file in
  let rec loop() =
    try
      let s = input_line fp in (s::loop())
    with _ -> []
  in loop()

let kill_z3() =
  (*   print_string ("killing z3 run by "^(string_of_int(!Global.config.pid))^"\n"); *)
  (* let _ = Unix.system ("ps xr | grep 'z3 z3"^(string_of_int(!Global.config.pid))^"' | awk '{print $1}' > pname; pkill -F pname > /dev/null 2>&1") in *)
  ()

   
open Async;;

let hoice_com solver ctx entry_funname entry_bounds is_need_example _ is_print_for_debug =
  (* set params *)
  let params = Params.mk_params ctx in
  Params.add_bool params (Symbol.mk_string ctx "print_fixedpoint_extensions") false;
  Z3.Fixedpoint.set_parameters solver params;
  (* make (assert (forall ((A Int)) (not (Entry_ A)))) *)
  (* (forall () entry_app) if bounds = [] *)
  let arg_names = List.mapi (fun idx _ -> "X" ^ (string_of_int idx)) entry_bounds in
  let entry_assert_str =
    Printf.sprintf "(assert (forall (%s) (not (%s))))"
      (String.concat " "
       @@ List.map (fun (var_name, (_, sort)) ->
           Printf.sprintf "(%s %s)" var_name (Z3.Sort.to_string @@ Z3interface.of_sort ctx sort))
       @@ Core.List.zip_exn arg_names entry_bounds)
      (String.concat " "
       @@ entry_funname :: arg_names)
  in
  (* make smt string *)
  let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
  let reg_forall = Str.regexp "^(forall " in
  let prefix = ref "" in
  let inputs =
    List.map
      (fun line ->
         if Str.string_match reg_assert line 0 then
           let matched_str = Str.matched_group 1 line in
           let line' = !prefix in
           line'
           ^
           if not @@ Str.string_match reg_forall matched_str 0 then (
             prefix := ")\n";
             "(assert (forall () " ^ matched_str
           )
           else (
             prefix := "";
             line
           )
         else
           line
      )
    @@ String.split_on_char '\n'
    @@ Fixedpoint.to_string solver
  in
  let inputs = inputs @ [
      !prefix;
      entry_assert_str;
      "(check-sat)";
    ]
  in
  let inputs = if is_need_example then
      "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
    else
      inputs
  in
  let inputs = inputs @ ["(exit)"] in
  if !Global.config.verbose && is_print_for_debug then
    (Debug.print @@ Printf.sprintf "Horn Clause (hoice):";
     Debug.print @@ Printf.sprintf "%s" @@ String.concat "\n" inputs;
    ()(*flush stderr*));
  let (hoice_infile,hoice_outfile) =
    let s = "hoice"^(string_of_int (get_fileid())) in
    (s^"in.smt2", s^"out.txt")
  in
  let _ = write_strings inputs hoice_infile in
   Unix.system ("hoice "^hoice_infile^" > "^hoice_outfile) 
  >>| (fun _ ->
        try
          let result = read_strings hoice_outfile in
          ("hoice", get_status_from_hoice_output result)
          with _ -> ("hoice", Status.Unknown))


let z3_com solver ctx entry_funname entry_bounds _ _ _ =
  let params = Params.mk_params ctx in
  Params.add_bool params (Symbol.mk_string ctx "print_fixedpoint_extensions") false;
  Z3.Fixedpoint.set_parameters solver params;
  (*
  print_string "===============\n";
  print_string ((Fixedpoint.to_string solver)^"\n");
   *)
  let inputs = [Fixedpoint.to_string solver]
  in
  let arg_names = List.mapi (fun idx _ -> "X" ^ (string_of_int idx)) entry_bounds in
  let entry_assert_str =
    if arg_names=[] then
      Printf.sprintf "(assert (not %s))"
      (String.concat " "
       @@ entry_funname :: arg_names)
    else
      Printf.sprintf "(assert (forall (%s) (not (%s))))"
      (String.concat " "
       @@ List.map (fun (var_name, (_, sort)) ->
           Printf.sprintf "(%s %s)" var_name (Z3.Sort.to_string @@ Z3interface.of_sort ctx sort))
       @@ Core.List.zip_exn arg_names entry_bounds)
      (String.concat " "
       @@ entry_funname :: arg_names)
  in
  let inputs = inputs @ [
      entry_assert_str;
      "(check-sat)";
    ]
  in
  let (z3_infile,z3_outfile) =
    let s = "z3"^(string_of_int(!Global.config.pid))^"_"^(string_of_int (get_fileid())) in
    (s^"in.smt2", s^"out.txt")
  in
  let _ = write_strings inputs z3_infile in
  print_endline (String.concat "," inputs);
  (print_string ((Core.Pid.to_string(Unix.getpid()))^"\n");
     Unix.system ("z3 "^z3_infile^" > "^z3_outfile))
  >>| (fun _ ->
       try
         let result = read_strings z3_outfile in
         ("z3", get_status_from_z3_output result)
        with _ -> ("z3", Status.Unknown))


let solve_onlynu_onlyforall_z3 _ timeout is_print_for_debug hes =
  assert (Hesutil.is_onlyforall hes);
  assert (HesLogic.is_onlynu hes);
  let hes = Hesutil.move_quantifiers_to_front (Hesutil.get_dual_hes hes) in
  let options = [] in
  let ctx = mk_context options in
  let funcs = HesLogic.get_functions hes in
  (* make environment for functions *)
  let penv = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let symbol = match pvar with Ident.Pvar name ->
        Z3.Symbol.mk_string ctx name
      in
      let args = HesLogic.get_args_of_function func in
      let arg_sorts = List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) args in
      let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
      (pvar, func_decl)
    ) funcs
  in
  (* make derivations from functions *)
  let derivations = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let args = HesLogic.get_args_of_function func in
      let body = HesLogic.get_body_of_function func in
      let env = List.rev args in
      Z3interface.of_formula ctx env penv
      @@ Formula.mk_imply
        body
        (Formula.mk_atom
           (Atom.mk_app
              (Predicate.mk_var pvar
                 (List.map (fun (_, sort) -> sort) args))
              (List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) args)
              Dummy)
           Dummy)
        Dummy
    ) funcs in
  (* make a derivation and a rel from the entry point *)
  let entry = HesLogic.get_entrypoint hes in
  let bounds, entry =
    if Formula.is_exists entry then
      let bounds, body, _ = Formula.let_exists entry in
      bounds, body
    else
      [], entry
  in
  let entry_funname = "Entry_" in
  let entry_fun = FuncDecl.mk_func_decl ctx
      (Symbol.mk_string ctx entry_funname)
      (List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) bounds)
      (Boolean.mk_sort ctx)
  in
  let env = List.rev bounds in
  let entry = Z3interface.of_formula ctx env penv entry in
  let entry_app =
    (Z3.Expr.mk_app ctx entry_fun
       (List.rev
          (List.mapi
             (fun i (_, sort) ->
                Quantifier.mk_bound ctx i (Z3interface.of_sort ctx sort)) (List.rev bounds))))
  in
  let derivations =
    (Z3.Boolean.mk_implies ctx entry entry_app)
    :: derivations
  in
  (* make solver *)
  let solver = Fixedpoint.mk_fixedpoint ctx in
  (* register functions (or relations) *)
  List.iter (fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
  Z3.Fixedpoint.register_relation solver entry_fun;
  (* register derivations *)
  List.iter (fun c -> Z3.Fixedpoint.add_rule solver c None) derivations;
  (* query *)
  (*
  let hoice_command = hoice_com solver ctx entry_funname bounds false timeout is_print_for_debug in
   *)
   print_endline "AAA";
  (if !Global.config.usehoice then
     hoice_com solver ctx entry_funname bounds false timeout is_print_for_debug
   else z3_com solver ctx entry_funname bounds false timeout is_print_for_debug)
  >>| (fun (_,r) -> r)

let solve_onlymu_onlyexists_par _ timeout is_print_for_debug hes =
  assert (Hesutil.is_onlyexists hes);
  assert (HesLogic.is_onlymu hes);
  let hes = Hesutil.move_quantifiers_to_front hes in
  let options = [] in
  let ctx = mk_context options in
  let funcs = HesLogic.get_functions hes in
  (* make environment for functions *)
  let penv = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let symbol = match pvar with Ident.Pvar name ->
        Z3.Symbol.mk_string ctx name
      in
      let args = HesLogic.get_args_of_function func in
      let arg_sorts = List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) args in
      let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
      (pvar, func_decl)
    ) funcs
  in
  (* make derivations from functions *)
  let derivations = List.map (fun func ->
      let pvar = HesLogic.get_pvar_of_function func in
      let args = HesLogic.get_args_of_function func in
      let body = HesLogic.get_body_of_function func in
      let env = List.rev args in
      Z3interface.of_formula ctx env penv
      @@ Formula.mk_imply
        body
        (Formula.mk_atom
           (Atom.mk_app
              (Predicate.mk_var pvar
                 (List.map (fun (_, sort) -> sort) args))
              (List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) args)
              Dummy)
           Dummy)
        Dummy
    ) funcs in
  (* make a derivation and a rel from the entry point *)
  let entry = HesLogic.get_entrypoint hes in
  let bounds, entry =
    if Formula.is_exists entry then
      let bounds, body, _ = Formula.let_exists entry in
      bounds, body
    else
      [], entry
  in
  let entry_funname = "Entry_" in
  let entry_fun = FuncDecl.mk_func_decl ctx
      (Symbol.mk_string ctx entry_funname)
      (List.map (fun (_, sort) -> Z3interface.of_sort ctx sort) bounds)
      (Boolean.mk_sort ctx)
  in
  let env = List.rev bounds in
  let entry = Z3interface.of_formula ctx env penv entry in
  let entry_app =
    (Z3.Expr.mk_app ctx entry_fun
       (List.rev
          (List.mapi
             (fun i (_, sort) ->
                Quantifier.mk_bound ctx i (Z3interface.of_sort ctx sort)) (List.rev bounds))))
  in
  let derivations =
    (Z3.Boolean.mk_implies ctx entry entry_app)
    :: derivations
  in
  (* make solver *)
  let solver = Fixedpoint.mk_fixedpoint ctx in
  (* register functions (or relations) *)
  List.iter (fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
  Z3.Fixedpoint.register_relation solver entry_fun;
  (* register derivations *)
  List.iter (fun c -> Z3.Fixedpoint.add_rule solver c None) derivations;
  (* query *)
  let hoice_command = hoice_com solver ctx entry_funname bounds false timeout is_print_for_debug in
  let z3_command = z3_com solver ctx entry_funname bounds false timeout is_print_for_debug in 
  let dresult = Deferred.any [hoice_command; z3_command] in
  dresult >>| (fun (_, result) -> Status.flip result)

let solve_onlynu_onlyforall_par is_need_example timeout is_print_for_debug hes =
  solve_onlymu_onlyexists_par is_need_example timeout is_print_for_debug ( Hesutil.get_dual_hes hes)
  >>| (fun r -> Status.flip r)

    
