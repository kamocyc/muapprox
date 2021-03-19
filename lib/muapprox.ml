module Util        = Hflmc2_util
module Syntax      = Hflmc2_syntax
module Options     = Hflmc2_options
module Manipulate  = Manipulate
module Ltl_print_syntax = Ltl_program.Print_syntax

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

let times = Hashtbl.create (module String)
let add_mesure_time tag f =
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let all_start = Unix.gettimeofday ()
let report_times () =
  let total = Unix.gettimeofday() -. all_start in
  let kvs = Hashtbl.to_alist times @ [("total", total)] in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

let show_result = Muapprox_prover.Status.string_of

let check_predicate_name (_, psi) =
  List.iter
    psi
    ~f:(fun {Hflz.var; _} ->
      if var.name ="Sentry" then failwith "You cannot use name \"Sentry\" except the first predicate."
    )
  
let parse file is_hes =
  let psi = 
    if is_hes then (
      let psi =
        match Hes.HesParser.from_file file with
        | Ok hes -> Muapprox_prover.Hflz_convert.of_hes hes
        | Error _ -> failwith "hes_parser" in
      Log.app begin fun m -> m ~header:"hes Input" "%a" Print.(hflz_hes simple_ty_) psi end;
      psi
    ) else (
      let psi, _ = Syntax.parse_file file in
      Log.app begin fun m -> m ~header:"Input" "%a" Print.(hflz_hes simple_ty_) psi end;
      psi
    ) in
  check_predicate_name psi;
  psi

let get_solve_options file =
  let open Muapprox_prover.Solve_options in
  {
    no_backend_inlining = !Options.no_backend_inlining;
    no_disprove = true;
    timeout = !Options.timeout;
    print_for_debug = !Options.print_for_debug;
    oneshot = !Options.oneshot;
    separate_original_formula_in_exists = not !Options.no_separate_original_formula_in_exists;
    solver = get_solver !Options.solver;
    first_order_solver = get_first_order_solver !Options.first_order_solver;
    solver_backend = get_solver_backend !Options.solver_backend (get_solver !Options.solver);
    coe = get_coe !Options.coe;
    dry_run = !Options.dry_run;
    no_simplify = !Options.no_simplify;
    stop_on_unknown = !Options.stop_on_unknown;
    pid = Unix.getpid();
    file = file;
    always_approximate = !Options.always_approximate;
    assign_values_for_exists_at_first_iteration = !Options.assign_values_for_exists_at_first_iteration;
    default_lexicographic_order = !Options.default_lexicographic_order;
    use_simple_encoding_when_lexico_is_one  = !Options.use_simple_encoding_when_lexico_is_one;
    disable_lexicographic = !Options.disable_lexicographic;
  }

let check_format file format_type =
  (* TODO: not use boolean to add more formats *)
  match format_type with 
  | "hes" -> true
  | "in"  -> false
  | "auto" -> begin
    (* TODO: improve *)
    let in_channel = open_in file in
    let is_hes = ref true in
    (try
      while true do
        let line = input_line in_channel in
        if Stdlib.String.trim line = "%HES" then (
          is_hes := false;
          raise End_of_file
        ) else if Stdlib.String.trim line = "s.t." || Stdlib.String.trim line = "where" then (
          is_hes := true;
          raise End_of_file
        )
      done
    with End_of_file ->
      close_in in_channel);
    !is_hes
  end
  | _ -> failwith "format should be \"hes\", \"in\" or \"auto\""

let main file cont =
  let solve_options = get_solve_options file in
  let is_hes = check_format file !Options.format in
  let psi = parse file is_hes in
  (* coefficients's default values are 1, 1 (defined in solve_options.ml) *)
  let coe1, coe2 = solve_options.coe in
  (* for debug *)
  (* let psi = if inlining then (
    let psi = Syntax.Trans.Simplify.hflz_hes psi inlining in
    Log.app begin fun m -> m ~header:"Simplified" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi
  ) else psi in *)
  Muapprox_prover.check_validity coe1 coe2 solve_options psi (fun (s1, info) -> cont (s1, info))

let assign_serial_to_vars_hes = Muapprox_prover.Check_formula_equality.assign_serial_to_vars_hes
let check_equal_hes = Muapprox_prover.Check_formula_equality.check_equal_hes
let show_debug_context = Muapprox_prover.show_debug_context
let abbrev_variable_numbers_hes = Muapprox_prover.Abbrev_variable_numbers.abbrev_variable_numbers_hes
let convert_ltl = Ltl_program.convert_ltl
let convert_all = Ltl_program.convert_all
let ltl_parse_file = Ltl_program.parse_file
let eliminate_unused_argument = Ltl_program.eliminate_unused_argument
let infer_type = Ltl_program.infer_type
let abbrev_variable_names = Ltl_program.abbrev_variable_names
let branching_time_program = Branching_time_program.branching_time_program
