open Config

exception Error of string

let subcmds = [
  ("--algorithm <algorithm>", "-a", "specify algorithm [cegis/ranking-function/rec-limit/rec-limit-simple] (default: cegis)");
  ("--format <format>", "-f", "specify format of input file [raw/smt-lib2/sygus-inv/clp/hes/c-ctl/c-ltl] (default: raw)");
  ("--mode", "-m", "specify mode [prove/disprove] (default:prove)");
  ("--problem", "-pr", "select a problem type [validity/psat/hes/dual-hes/optimized-hes/optimized-dual-hes] (default:validity)");
  ("--verbose", "-v", "enable verbose mode");
  ("--mkbenchinfo <outfile>", "-mbi", "save information of benchmark into <outfile>");
  ("--template-shape", "-ts", "choose the shape of predicate templates from [linear/dnf] (default:linear)");
  ("--qualifier-domain", "-qd", "choose the domain of qualifiers from [octagon/octahedron] (default:octagon)");
  ("--number-of-conj", "-nc", "parameter for dnf template (default:2)");
  ("--number-of-disj", "-nd", "parameter for dnf template (default:2)");
  ("--synthesizer", "-synth", "[tb/scqm/dt/ltb/pasid/pasat/tb+dt/tb+dt+pasat] (default:tb)");
  ("--coe <a>,<b>", "-c", "parameter for estimation of rec times for rec-limit solver: ax + b");
  ("--encoding-mode", "-e", "mode to encode exists for rec-limit solver [mu/mus/nu] (default:nu)");
  ("--disable-free-variable-elimination", "-dfve", "disable free term variable elimination in fixpoint predicates (cegis prover)");
  ("--enable-undecided-bool-expansion", "-eube", "enable undecided boolean variable expansion");
  ("--enable-smart-model", "-esm", "enable smart z3 model");
  ("--enable-preprocess", "-epp", "enable preprocessing");
  ("--check-answer", "-ca", "substitute the answer into problem and check");
  ("--complete-solution", "-cs", "complete elimed predicates by preprocess");
  ("--enable-default-qualifier", "-edq", "enable default qualifier");
  ("--enable-dim-reduction", "-edr", "enable demension reduction for PASIDSynth.");
  ("--dt-reduction", "-dtr", "enable qualifier reduction for decision tree synthesizer");
  ("--disable-coeff-restriction", "-dcr", "disable coefficients restriction");
  ("--coeff-restriction-strategy <n>", "-crs", "iteratively find coeffs whose absolute value is not greater than 2^i for each i=0,...,n-1 (default:2)");
  ("--example-restriction", "-exr", "enable example restriction");
  ("--debug-print-z3-input", "-dp-zi", "print input formulas to Z3 (for debug)");
  ("--debug-print-z3-model", "-dp-zm", "print model from Z3 solver (for debug)");
  ("--output-iteration", "-oi", "enable output iteration");
  ("--multisol", "-sol", "number of solution");
  ("--resolution-threshold", "-rt", "threshold for resolution");
  ("--help", "-h", "show help, and quit");
]

let show_usage out_channel =
  let subcmd_desc =
    String.concat "\n" @@ List.map (fun (name, sname, desc) -> "  " ^ name ^ ", " ^ sname ^ "\t" ^ desc) subcmds
  in
  output_string out_channel (Printf.sprintf "\
Usage: %s [options] <filename>
where options are
%s
" Sys.argv.(0) subcmd_desc)

let show_unknown_warning arg = Printf.eprintf "\
invalid commandline argument: %s
`%s --help` to read usage\n" arg Sys.argv.(0)

let format_of_string = function
  | "raw" -> Raw
  | "hes" -> Hes
  | "smt-lib2" -> SmtLib2
  | "sygus-inv" -> SyGuSInv
  | "clp" -> CLP
  | "c-ctl" -> CCTL
  | "c-ltl" -> CLTL
  (* add other formats for benchmarks *)
  | fmt -> raise (Error (Printf.sprintf "invalid format: %s" fmt))

let algorithm_of_string = function
  | "cegis" -> CEGIS
  | "ranking-function" -> RankingFunction
  | "rec-limit" -> RecLimit
  | "rec-limit-simple" -> SimpleRecLimit
  | name -> raise (Error (Printf.sprintf "invalid algorithm: %s" name))

let mode_of_string = function
  | "prove" -> Prove
  | "disprove" -> Disprove
  | "parallel" -> Parallel
  | mode -> raise (Error (Printf.sprintf "invalid mode: %s" mode))

let shape_of_string = function
  | "linear" -> LinearTemplate
  | "dnf"    -> DNFTemplate
  | others   -> raise (Error (Printf.sprintf "invalid shape: %s" others))

let domain_of_string = function
  | "octagon" -> Octagon
  | "octahedron" -> Octahedron
  | others   -> raise (Error (Printf.sprintf "invalid domain: %s" others))

let synthesizer_of_string = function
  | "tb" -> TBSynth
  | "scqm" -> SCQMSynth
  | "dt" -> DTSynth
  | "ltb" -> LTBSynth
  | "pasid" -> PASIDSynth
  | "pasat" -> PASATSynth
  | "tb+dt" -> TB_DTSynth
  | "tb+dt+pasat" -> TB_DT_PASATSynth
  | synth -> raise (Error (Printf.sprintf "invalid synthesizer: %s" synth))

let problem_of_string = function
  | "validity" -> Validity
  | "psat" -> PSAT
  | "hes" -> ConvertToHes
  | "dual-hes" -> ConvertToDualHes
  | "optimized-hes" -> ConvertToOptimizedHes
  | "optimized-dual-hes" -> ConvertToOptimizedDualHes
  | problem -> raise (Error (Printf.sprintf "invalid problem type: %s" problem))

let coe_of_string coe_str =
  if Str.string_match (Str.regexp "^\\(-?[0-9]+\\),\\(-?[0-9]+\\)$") coe_str 0 then
    let a = int_of_string @@ Str.matched_group 1 coe_str in
    let b = int_of_string @@ Str.matched_group 2 coe_str in
    (a, b)
  else
    raise (Error (Printf.sprintf "the format of coe must be of <a>,<b> but %s" coe_str))

let encoding_mode_of_string = function
  | "mu" -> Mu
  | "mus" -> Mus
  | "nu" -> Nu
  | others -> raise (Error (Printf.sprintf "invalid encoding mode: %s" others))

let check_error config =
  if config.filename = filename_unspecified then
    raise (Error "<filename> is empty")

let parse args =
  let rec aux args config = match args with
    | [] -> config
    | fname :: args when fname.[0] <> '-' ->
      config |> update_filename fname |> aux args

    | "--format" :: fmt :: args
    | "-f" :: fmt :: args ->
      config |> update_format (format_of_string @@ String.lowercase_ascii fmt) |> aux args

    | "--problem" :: problem :: args
    | "-pr" :: problem :: args ->
      config |> update_problem (problem_of_string @@ String.lowercase_ascii problem) |> aux args

    | "--verbose" :: args
    | "-v" :: args ->
      config |> update_verbose true |> aux args

    | "--algorithm" :: algorithm_name :: args
    | "-a" :: algorithm_name :: args ->
      config |> update_algorithm (algorithm_of_string @@ String.lowercase_ascii algorithm_name)
      |> aux args

    | "--mode" :: mode :: args
    | "-m" :: mode :: args ->
      config |> update_mode (mode_of_string @@ String.lowercase_ascii mode) |> aux args

    | "--mkbenchinfo" :: outfile :: args
    | "-mbi" :: outfile :: args ->
      config |> update_mk_bench_info (Some outfile) |> aux args

    | "--template-shape" :: shape :: args
    | "-ts" :: shape :: args ->
      config |> update_template_shape (shape_of_string @@ String.lowercase_ascii shape)
      |> aux args

    | "--qualifier-domain" :: domain :: args
    | "-qd" :: domain :: args ->
      config |> update_qualifier_domain (domain_of_string @@ String.lowercase_ascii domain)
      |> aux args

    | "--number-of-disj" :: nd :: args
    | "-nd" :: nd :: args ->
      config |> update_number_of_disj (int_of_string nd) |> aux args

    | "--number-of-conj" :: nc :: args
    | "-nc" :: nc :: args ->
      config |> update_number_of_conj (int_of_string nc) |> aux args

    | "--synthesizer" :: synth :: args
    | "-synth" :: synth :: args ->
      config |> update_synthesizer (synthesizer_of_string @@ String.lowercase_ascii synth)
      |> aux args

    | "--coe" :: coe :: args
    | "-c" :: coe :: args ->
      config |> update_coe (Some (coe_of_string coe)) |> aux args

    | "--encoding-mode" :: e :: args
    | "-e" :: e :: args ->
      config |> update_encoding_mode (encoding_mode_of_string e) |> aux args

    | "--disable-free-variable-elimination" :: args
    | "-dfve" :: args ->
      config |> disable_free_variable_elimination |> aux args

    | "--enable-undecided-bool-expansion" :: args
    | "-eube" :: args ->
      config |> enable_undecided_bool_expansion |> aux args

    | "--enable-smart-model" :: args
    | "-esm" :: args ->
      config |> enable_smart_model |> aux args

    | "--enable-preprocess" :: args
    | "-epp" :: args ->
      config |> enable_preprocess |> aux args

    | "--enable-dim-reduction" :: args
    | "-edr" :: args ->
      config |> enable_dim_reduction |> aux args

    | "--complete-solution" :: args
    | "-cs" :: args ->
      config |> enable_complete_solution |> aux args

    | "--check-answer" :: args
    | "-ca" :: args ->
      config |> enable_check_ans |> aux args

    | "--enable-default-qualifier" :: args
    | "-edq" :: args ->
      config |> enable_default_qualifier |> aux args

    | "--dt-reduction" :: args
    | "-dtr" :: args ->
      config |> enable_dt_reduction |> aux args

    | "--disable-coeff-restriction" :: args
    | "-dcr" :: args ->
      config |> disable_coeff_restriction |> aux args

    | "--coeff-restriction-strategy" :: nc :: args
    | "-crs" :: nc :: args ->
      config |> update_coeff_restriction_strategy (int_of_string nc) |> aux args

    | "--example-restriction" :: args
    | "-exr" :: args ->
      config |> enable_example_restriction |> aux args

    | "--debug-print-z3-input" :: args
    | "-dp-zi" :: args ->
      config |> enable_debug_print_z3_input |> aux args

    | "--debug-print-z3-model" :: args
    | "-dp-zm" :: args ->
      config |> enable_debug_print_z3_model |> aux args

    | "--output-iteration" :: args
    | "-oi" :: args ->
      config |> enable_output_iteration |> aux args

    | "--multisol" :: sol :: args
    | "-sol" :: sol :: args ->
      config |> update_multisol (int_of_string sol) |> aux args

    | "--resolution-threshold" :: rt :: args
    | "-rt" :: rt :: args ->
      config |> update_resolution_threshold (int_of_string rt) |> aux args

    | "--help" :: _ | "-h" :: _ ->
      show_usage stdout; exit 1

    | x :: _ ->
      show_unknown_warning x; exit 1

  in let config = make_default () |> aux args
  in check_error config; config
