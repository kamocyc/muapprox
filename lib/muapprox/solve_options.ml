type solver_type = Iwayama | Katsura

type options = 
  {
    no_backend_inlining : bool;
    timeout : float;
    print_for_debug : bool;
    oneshot : bool;
    separate_original_formula_in_exists : bool;
    solver : solver_type
  }

let get_solver solver_name = 
  match solver_name with
  | "iwayama" -> Iwayama
  | "katsura" -> Katsura
  | s -> failwith @@ "unknown solver \"" ^ s ^ "\""
