type solver_type = Iwayama | Katsura
type first_order_solver_type = FptProverRecLimit

type options = 
  {
    no_backend_inlining : bool;
    timeout : float;
    print_for_debug : bool;
    oneshot : bool;
    separate_original_formula_in_exists : bool;
    solver : solver_type;
    first_order_solver: first_order_solver_type option;
    coe : int * int;
    dry_run : bool;
    no_simplify: bool;
    ignore_unknown: bool;
  }

let get_solver solver_name = 
  match solver_name with
  | "iwayama" -> Iwayama
  | "katsura" -> Katsura
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\""

let get_first_order_solver use_fo_solver = 
  if use_fo_solver then Some FptProverRecLimit else None
  
(* let get_first_order_solver solver_name =
  match solver_name with
  | "fptprover-rec-limit" -> Some FptProverRecLimit
  | "" -> None
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\"" *)

let get_coe coe_opt = 
  match String.trim coe_opt with
  | "" -> (1, 1)
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