type format =
  | Raw (* first-order fixpoint logic that we prove directly *)
  | Hes (* hes that we prove directly  *)
  | SmtLib2 (* for benchmark *)
  | CLP (* Constraint Logic Programming *)
  | SyGuSInv (* for SyGuS Invariant Synthesis Truck benchmarks *)
  | CCTL (* for ctl benchmarks written in c *)
  | CLTL (* for ltl benchmarks written in c *)
(* add other formats for benchmarks *)

type timeout = {
  z3: int;
  (* TODO: add other solver's timeout *)
}

type algorithm =
  | CEGIS
  | RankingFunction
  | RecLimit
  | SimpleRecLimit
  (* add other algorithms *)

type synthesizer =
  | TBSynth
  | DTSynth
  | SCQMSynth
  | LTBSynth
  | PASIDSynth
  | PASATSynth
  | TB_DTSynth
  | TB_DT_PASATSynth

type problem =
  | PSAT
  | Validity
  | ConvertToHes

type mode =
  | Prove
  | Disprove
  | Parallel

type template_shape =
  | LinearTemplate
  | DNFTemplate

type qualifier_domain =
  | Octahedron
  | Octagon

type encoding_mode =
  | Mu
  | Mus
  | Nu

type t = {
  timeout : timeout;
  filename: string;
  fmt: format;
  verbose: bool;
  pid: int;
  usehoice: bool;
  algorithm: algorithm;
  mode: mode;
  mk_bench_info: string option;
  template_shape: template_shape;
  qualifier_domain: qualifier_domain;
  number_of_conj: int;
  number_of_disj: int;
  synthesizer: synthesizer;
  coe: (int * int) option;
  encoding_mode: encoding_mode;
  free_variable_elimination: bool;
  undecided_bool_expansion: bool;
  smart_model : bool;
  preprocess : bool;
  complete_solution : bool;
  check_ans : bool;
  default_qualifier : bool;
  dt_reduction: bool;
  coeff_restriction: bool;
  coeff_restriction_strategy: int list;
  example_restriction: bool;
  debug_print_z3_input : bool;
  debug_print_z3_model : bool;
  problem: problem;
  output_iteration: bool;
  multisol: int;
  resolution_threshold: int;
  dim_reduction: bool;
}

let filename_unspecified = "<unspecified>"

let make_default () =
  {
    timeout = {
      z3 = 114514
    };
    filename = filename_unspecified;
    pid = Unix.getpid();
    algorithm = RecLimit;
    fmt = Hes;
    verbose = false;
    usehoice = false;
    mode = Prove;
    mk_bench_info = None;
    template_shape = LinearTemplate;
    qualifier_domain = Octagon;
    number_of_conj = 1;
    number_of_disj = 1;
    synthesizer = TBSynth;
    coe = None;
    encoding_mode = Nu;
    free_variable_elimination = true;
    undecided_bool_expansion = false;
    smart_model = false;
    preprocess = false;
    complete_solution = false;
    check_ans = false;
    default_qualifier = false;
    dt_reduction = false;
    coeff_restriction = true;
    coeff_restriction_strategy = [1; 2];
    example_restriction = false;
    debug_print_z3_input = false;
    debug_print_z3_model = false;
    problem = Validity;
    output_iteration = false;
    multisol = 1;
    resolution_threshold = 4;
    dim_reduction = false;
  }

let update_filename name config =
  { config with
    filename = name
  }

let update_format fmt config =
  { config with
    fmt = fmt
  }

let update_verbose v config =
  { config with
    verbose = v
  }

let update_hoice v config =
  { config with
    usehoice = v
  }

let update_algorithm algorithm config =
  { config with
    algorithm = algorithm
  }

let update_mode mode config =
  { config with
    mode = mode
  }

let update_mk_bench_info outfile config =
  { config with
    mk_bench_info = outfile
  }

let update_template_shape template_shape config =
  { config with template_shape = template_shape}

let update_qualifier_domain qualifier_domain config =
  { config with qualifier_domain = qualifier_domain}

let update_number_of_conj n_conj config =
  { config with number_of_conj = n_conj }

let update_number_of_disj n_disj config =
  { config with number_of_disj = n_disj }

let update_synthesizer synth config =
  { config with synthesizer = synth }

let update_coe coe config =
  { config with coe = coe }

let update_encoding_mode encoding_mode config =
  { config with encoding_mode = encoding_mode }

let disable_free_variable_elimination config =
  { config with free_variable_elimination = false }

let enable_undecided_bool_expansion config =
  { config with undecided_bool_expansion = true }

let enable_smart_model config =
  { config with smart_model = true }

let enable_preprocess config =
  { config with preprocess = true }

let enable_complete_solution config =
  { config with complete_solution = true }

let enable_check_ans config =
  { config with check_ans = true }

let enable_default_qualifier config =
  { config with default_qualifier = true }

let enable_dt_reduction config =
  { config with dt_reduction = true }

let disable_coeff_restriction config =
  { config with coeff_restriction = false }

let update_coeff_restriction_strategy n config =
  { config with coeff_restriction_strategy = List.init n (fun n -> 1 lsl n) }

let enable_example_restriction config =
  { config with example_restriction = true }

let enable_debug_print_z3_input config =
  { config with debug_print_z3_input = true }

let enable_debug_print_z3_model config =
  { config with debug_print_z3_model = true }

let update_problem problem config =
  { config with problem = problem }

let enable_output_iteration config =
  { config with output_iteration = true }

let update_multisol sol config =
  { config with multisol = sol }

let update_resolution_threshold rt config =
  { config with resolution_threshold = rt }

let enable_dim_reduction config =
  { config with dim_reduction = true }
