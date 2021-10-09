[@@@ocaml.warning "-39"]

open Hflmc2_util

(******************************************************************************)
(* Options                                                                    *)
(******************************************************************************)

let format = ref (Obj.magic())
let timeout = ref (Obj.magic())
let print_for_debug = ref (Obj.magic())
let no_backend_inlining = ref (Obj.magic())
let no_separate_original_formula_in_exists = ref (Obj.magic())
let solver = ref (Obj.magic())
let backend_solver = ref (Obj.magic())
let first_order_solver = ref (Obj.magic())
let coe = ref (Obj.magic())
let dry_run = ref (Obj.magic())
let oneshot = ref (Obj.magic())
let no_simplify = ref (Obj.magic())
let stop_on_unknown = ref (Obj.magic())
let always_approximate = ref (Obj.magic())
let assign_values_for_exists_at_first_iteration = ref (Obj.magic())
let default_lexicographic_order = ref (Obj.magic())
let simplify_bound = ref (Obj.magic())
let use_simple_encoding_when_lexico_is_one = ref (Obj.magic())
let disable_lexicographic = ref (Obj.magic())
let add_arguments = ref (Obj.magic())
let coe_arguments = ref (Obj.magic())
let no_elim = ref (Obj.magic())
let unused_arguments_elimination = ref (Obj.magic()) 
let adding_arguments_optimization = ref (Obj.magic ())
let use_all_variables = ref (Obj.magic())
let replacer = ref (Obj.magic())
let auto_existential_quantifier_instantiation = ref (Obj.magic())
let with_partial_analysis = ref (Obj.magic())
let with_usage_analysis = ref (Obj.magic())
let always_add_arguments = ref (Obj.magic())
let agg = ref (Obj.magic())
(******************************************************************************)
(* Parser                                                                     *)
(******************************************************************************)

let set_ref ref x = ref := x

type params =
  {
  input : string list [@pos 0] [@docv "FILE"]
  (** input file path *)
  
  ; format : string [@default "auto"]
  (** input file format ("auto" / "hes" / "in". Default is "auto") *)

  ; no_inlining_backend : bool [@default false]
  (** Disable inlining in a backend solver *)
  
  ; timeout : int [@default 360]
  (** Timeout for a backend solver *)
  
  ; print_for_debug : bool [@default true]
  (** Print for debug *)
  
  ; no_separate_original_formula_in_exists : bool [@default true]
  (** If specified, when approximating exists, do not create new predicate that reduces the formula size *)
  
  ; solver : string [@default "katsura"]
  (** Choose background nu-only-HFLz solver. Available: katsura, iwayama, suzuki *)
  
  ; backend_solver : string [@default ""]
  (** --solver option on the backend solver. (only used in the katsura solver) *)
  
  ; first_order_solver : bool [@default false]
  (** If true, use z3 or hoice to solve first-order formulas. If empty (or default), always use a solver for higher-order formulas. *)
  
  ; coe : string [@default ""]
  (** Initial coefficients for approximating mu and exists. Speficfy such as "1,8" (default is "1,1") *)
  
  ; dry_run : bool [@default false]
  (** Do not solve *)
  
  ; oneshot : bool [@default false]
  (** Try to solve only once **)
  
  ; no_simplify : bool [@default false]
  (** Do not simplify formula. It seems to get better results when false. (default: false) *)
  
  ; stop_on_unknown : bool [@default false]
  (** If false, skip "Unknown" result from a backend solver (the same behaviour as "Invalid" result). If true, stop solving when get "Unknown". (default: false) *)
  
  ; always_approximate : bool [@default false]
  (** Always approximate a HFLz formula even if the formula (or its dual) is v-HFLz. (debug purpose) *)
  
  ; instantiate_exists: bool [@defalut false]
  (** At the first iteration (coe1=1, coe2=1), assign concrete values to existentially quantified variables. *)
  
  ; lexicographic_order: int [@default 1]
  (** Default number of pairs when using lexicographic order *)
  
  ; simplify_bound : bool [@default false]
  (** Simplify bound formulas for approximating mu *)
  
  ; use_simple_encoding_when_lexico_is_one: bool [@default true]
  (** Use simple encoding when lexicographic order is one *)
  
  ; disable_lexicographic: bool [@default false]
  (** Disable trying encoding of lexicographic order *)
  
  ; disable_add_arguments : bool [@default false]
  (** Disable adding integer arguments that represent information of higher-order arguments *)
  
  ; coe_arguments : string [@default ""]
  (** Coefficients of added arguments (default: 1,0) *)
  
  ; no_elim : bool [@default false]
  (** DON'T eliminate mu and exists (debug purpose) *)
  
  ; no_adding_arguments_optimization : bool [@default false]
  (** DON'T analyze partial applications and unsed adding arguments to optimize added arguments *)
  
  ; use_all_variables : bool [@default false]
  (** Use all variables (not only variables which are occured in arguments of application) to guess a recursion bound to approximate least-fixpoints. (This may (or may not) help Hoice.) *)
  
  ; no_unused_arguments_elimination : bool [@default false]
  (** DON'T eliminate unused arguments using type-based analysis (when adding arguments, the solver always eliminates unused arguments ) *)
  
  ; replacer : string [@default ""]
  (** Ad-hoc replacement of approximated forumula (for katsura-solver only) *)
  
  ; no_auto_existential_quantifier_instantiation : bool [@default false]
  (** DON'T instantiate existential quantifiers even if instantiation seems to be effective *)
  
  ; no_partial_analysis : bool [@default false]
  
  ; no_usage_analysis : bool [@default false]
  
  ; always_add_arguments : bool [@default false]
  
  ; agg : bool [@default false]
  (* for debug *)
  }
[@@deriving cmdliner,show]

let set_up_params params =
  set_ref format                   params.format;
  set_ref timeout                  params.timeout;
  set_ref print_for_debug          params.print_for_debug;
  set_ref no_separate_original_formula_in_exists params.no_separate_original_formula_in_exists;
  set_ref no_backend_inlining      params.no_inlining_backend;
  set_ref solver                   params.solver;
  set_ref backend_solver           params.backend_solver;
  set_ref first_order_solver       params.first_order_solver;
  set_ref coe                      params.coe;
  set_ref dry_run                  params.dry_run;
  set_ref oneshot                  params.oneshot;
  set_ref no_simplify              params.no_simplify;
  set_ref stop_on_unknown           params.stop_on_unknown;
  set_ref always_approximate       params.always_approximate;
  set_ref assign_values_for_exists_at_first_iteration params.instantiate_exists;
  set_ref default_lexicographic_order params.lexicographic_order;
  set_ref simplify_bound       params.simplify_bound;
  set_ref use_simple_encoding_when_lexico_is_one params.use_simple_encoding_when_lexico_is_one;
  set_ref disable_lexicographic params.disable_lexicographic;
  set_ref coe_arguments params.coe_arguments;
  set_ref no_elim params.no_elim;
  set_ref use_all_variables params.use_all_variables;
  set_ref add_arguments (not params.disable_add_arguments);
  set_ref unused_arguments_elimination (not params.no_unused_arguments_elimination);
  set_ref adding_arguments_optimization (not params.no_adding_arguments_optimization);
  set_ref replacer params.replacer;
  set_ref auto_existential_quantifier_instantiation (not params.no_auto_existential_quantifier_instantiation);
  set_ref with_partial_analysis (not params.no_partial_analysis);
  set_ref with_usage_analysis (not params.no_usage_analysis);
  set_ref always_add_arguments params.always_add_arguments;
  set_ref agg params.agg;
  if params.disable_add_arguments && params.always_add_arguments then failwith "illegal parameter combination (disable_add_arguments and always_add_arguments)";
  params.input

(******************************************************************************)
(* Term                                                                       *)
(******************************************************************************)

let term_set_up_params () =
  Cmdliner.Term.(const set_up_params $ params_cmdliner_term ())

module Logs     = Logs
module Logs_cli = Logs_cli
module Logs_fmt = Logs_fmt

(* Log *)
  
let term_setup_log () =
  (*{{{*)
  let setup style_renderer level =
    Format.set_margin 1000;
    Fmt_tty.setup_std_outputs ?style_renderer ();
    
    let reporter = get_reporter "@[<v 2>[%a]@ @]" in
    Logs.set_reporter reporter;
    
    Logs.set_level level
  in
    Cmdliner.Term.(const setup $ Fmt_cli.style_renderer () $ Logs_cli.level ())
(*}}}*)

type input = [`File of string | `Stdin]
let parse ?argv () : input option =
  let term () =
    let open Cmdliner.Term in
    const (fun _ file -> file)
      $ term_setup_log () (* NOTE order matters *)
      $ term_set_up_params ()
  in match Cmdliner.Term.(eval ?argv (term (), info "muapprox")) with
  | `Ok [] -> Some `Stdin
  | `Ok [file] -> Some (`File file)
  | `Ok _ -> Fn.todo ~info:"multiple input files" ()
  | _     -> None

