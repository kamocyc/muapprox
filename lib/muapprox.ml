module Util        = Hflmc2_util
module Syntax      = Hflmc2_syntax
module Options     = Hflmc2_options
module Manipulate  = Manipulate
module Ltl_print_syntax = Ltl_program.Print_syntax

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

let log_string = Manipulate.Hflz_util.log_string Log.info

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
  
let parse file =
  let psi = 
    let psi, _ = Syntax.parse_file file in
    Log.info begin fun m -> m ~header:"Input" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi in
  check_predicate_name psi;
  psi

let get_solve_options file =
  let open Muapprox_prover.Solve_options in
  let approx_parameter, use_custom_parameter =
    get_approx_parameter !Options.coe !Options.coe_arguments !Options.default_lexicographic_order in
  {
    no_backend_inlining = !Options.no_backend_inlining;
    log_level = !Options.log_level;
    no_disprove = true;
    timeout = !Options.timeout;
    solver = get_solver !Options.solver;
    first_order_solver = get_first_order_solver !Options.first_order_solver;
    backend_solver = get_backend_solver !Options.backend_solver (get_solver !Options.solver);
    approx_parameter = approx_parameter;
    use_custom_parameter = use_custom_parameter;
    oneshot = use_custom_parameter || !Options.oneshot;
    dry_run = !Options.dry_run;
    eliminate_unused_arguments = !Options.eliminate_unused_arguments;
    stop_on_unknown = !Options.stop_on_unknown;
    pid = Unix.getpid();
    file = file;
    always_approximate = !Options.always_approximate;
    assign_values_for_exists_at_first_iteration = !Options.assign_values_for_exists_at_first_iteration;
    simplify_bound = !Options.simplify_bound;
    use_simple_encoding_when_lexico_is_one  = !Options.use_simple_encoding_when_lexico_is_one;
    disable_lexicographic = !Options.disable_lexicographic;
    add_arguments = !Options.add_arguments;
    no_elim = !Options.no_elim;
    use_all_variables = !Options.use_all_variables;
    replacer = !Options.replacer;
    auto_existential_quantifier_instantiation = !Options.auto_existential_quantifier_instantiation;
    with_partial_analysis = !Options.with_partial_analysis;
    with_usage_analysis = !Options.with_usage_analysis;
    always_add_arguments = !Options.always_add_arguments;
    z3_path = !Options.z3_path;
    no_temp_files = !Options.no_temp_files;
    try_weak_subtype = !Options.try_weak_subtype;
    backend_options = !Options.backend_options;
  }

let simplify_agg_ hes =
  let hes = Manipulate.Hes_optimizer.simplify_all hes in
  let hes = Manipulate.Hes_optimizer.simplify_agg false hes in
  let path =
    let r = Random.int 0x10000000 in
    Printf.sprintf "/tmp/%d.tmp" r in
  ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:path ~without_id:false true hes;
  log_string @@ "simplified formula: " ^ path;
  let hes = parse path in
  hes
  
let main file cont =
  let solve_options = get_solve_options file in
  log_string @@ "z3_path: " ^ solve_options.z3_path;
  let psi = parse file in
  (* coefficients's default values are 1, 1 (defined in solve_options.ml) *)
  (* for debug *)
  (* let psi = if inlining then (
    let psi = Syntax.Trans.Simplify.hflz_hes psi inlining in
    Log.info begin fun m -> m ~header:"Simplified" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi
  ) else psi in *)
  let psi =
    if !Options.eliminate_unused_arguments || !Options.aggressive_simplification then
      Ltl_program.eliminate_unused_argument psi
    else psi in
  let psi = if !Options.aggressive_simplification then simplify_agg_ psi else psi in
  Muapprox_prover.check_validity solve_options psi (fun (s1, info) -> cont (s1, info))

let assign_serial_to_vars_hes = Muapprox_prover.Check_formula_equality.assign_serial_to_vars_hes
let check_equal_hes = Muapprox_prover.Check_formula_equality.check_equal_hes
let show_debug_context = Muapprox_prover.show_debug_context
let show_debug_contexts = Muapprox_prover.show_debug_contexts
let abbrev_variable_numbers_hes = Muapprox_prover.Abbrev_variable_numbers.abbrev_variable_numbers_hes
let convert_ltl = Ltl_program.convert_ltl
let convert_all = Ltl_program.convert_all
let ltl_parse_file = Ltl_program.parse_file
let eliminate_unused_argument = Ltl_program.eliminate_unused_argument
let infer_type = Ltl_program.infer_type
let abbrev_variable_names = Ltl_program.abbrev_variable_names
let branching_time_program = Branching_time_program.branching_time_program
let convert_nu_hflz_to_program_with_exception = Muapprox_prover.Mochi_solver.convert_nu_hflz_to_program_with_exception
