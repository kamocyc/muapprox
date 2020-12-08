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
    first_order_solver: first_order_solver_type option 
  }

let get_solver solver_name = 
  match solver_name with
  | "iwayama" -> Iwayama
  | "katsura" -> Katsura
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\""

let get_first_order_solver solver_name =
  match solver_name with
  | "fptprover-rec-limit" -> Some FptProverRecLimit
  | "" -> None
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\""