type solver_type = Iwayama | Katsura | Suzuki
type first_order_solver_type = FptProverRecLimit

type approx_parameter = {
  coe1: int;
  coe2: int;
  add_arg_coe1: int;
  add_arg_coe2: int;
  lexico_pair_number: int;
}

type options = 
  {
    no_backend_inlining : bool;
    no_disprove: bool;
    timeout : int;
    approx_parameter: approx_parameter;
    use_custom_parameter: bool;
    oneshot: bool;
    print_for_debug : bool;
    separate_original_formula_in_exists : bool;
    solver : solver_type;
    backend_solver: string option;
    first_order_solver: first_order_solver_type option;
    dry_run : bool;
    no_simplify: bool;
    stop_on_unknown: bool;
    pid: int;
    file: string;
    always_approximate: bool;
    assign_values_for_exists_at_first_iteration: bool;
    simplify_bound: bool;
    use_simple_encoding_when_lexico_is_one: bool;
    disable_lexicographic: bool;
    add_arguments: bool;
    no_elim: bool;
    unused_arguments_elimination: bool;
    adding_arguments_optimization: bool;
    use_all_variables: bool;
    replacer: string;
    auto_existential_quantifier_instantiation: bool;
  }
let get_solver solver_name = 
  match solver_name with
  | "iwayama" -> Iwayama
  | "katsura" -> Katsura
  | "suzuki"  -> Suzuki
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\""

let get_first_order_solver use_fo_solver = 
  if use_fo_solver then Some FptProverRecLimit else None
  
let get_backend_solver s solver =
  match solver with
  | Katsura -> begin
    (* backend-solver option is only for katsura-solver *)
    let s = String.trim s in
    match s with
    | "" -> None
    | s -> Some s
  end
  | _ -> Some "hoice" (* set a random value *)

let get_coe coe_opt = 
  match String.trim coe_opt with
  | "" -> failwith "get_coe: should not be blank"
  | c -> begin
    match String.split_on_char ',' c with
    | [c1; c2] -> begin
      try
        (int_of_string c1, int_of_string c2)
      with Failure _ -> 
        failwith "get_coe: Format error. format of coefficients is like \" 2,10 \""
    end
    | _ -> failwith "get_coe: Format error. format of coefficients is like \" 2,10 \""
  end

let get_approx_parameter coe add_arg_coe default_lexicographic_order =
  let default = {
    coe1 = 1;
    coe2 = 1;
    add_arg_coe1 = 0;
    add_arg_coe2 = 0;
    lexico_pair_number = 1
  } in
  match coe, add_arg_coe, default_lexicographic_order with
  | ("", "", 1) ->
    (* this default values will be overwritten in muappprox_prover.ml *)
    default, false
  | _ -> begin
    let coe1, coe2 =
      match coe with
      | "" ->
        default.coe1, default.coe2
      | _ -> get_coe coe in
    let add_arg_coe1, add_arg_coe2 =
      match add_arg_coe with
      | "" ->
        default.add_arg_coe1, default.add_arg_coe2
      | _ -> get_coe add_arg_coe in
    let lexico_pair_number = default_lexicographic_order in
    {
      coe1 = coe1;
      coe2 = coe2;
      add_arg_coe1 = add_arg_coe1;
      add_arg_coe2 = add_arg_coe2;
      lexico_pair_number = lexico_pair_number
    }, true
  end
