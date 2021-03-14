open Program
open Itype
open Trans_ltl

let as_function assoc key =
  match List.find_opt (fun (k, s) -> k = key) assoc with
  | None -> failwith @@ "as_function: Not_found (key=" ^ show_state key ^ ")"
  | Some (_, s) -> s

let as_multi_function assoc key =
  match List.find_all (fun (k, v) -> k = key) assoc with
  | [] -> failwith @@ "as_multi_function (key=(" ^ show_state (fst key) ^ ", " ^ show_symbol (snd key) ^ "))"
  | l -> l |> List.map (fun (k, v) -> v)

let show_priority func_priority =
  "[\n" ^
  (List.map (fun (id, p) -> Hflmc2_syntax.Id.to_string ~without_id:true id ^ " -> " ^ string_of_int p) func_priority |> String.concat ";\n") ^
  "\n]"
  
let set_id_on_env (env : itype_env) program' =
  let open Hflmc2_syntax.Id in
  List.map (fun (e, t) ->
    match List.find_opt (fun {var} -> var.name = e.name) (snd program') with
    | Some p -> ({e with id = p.var.id}, t)
    | None -> failwith "set_id_on_env"
  ) env
  
let convert_ltl file show_raw_id_name always_use_canonical_type_env encode_nondet_with_forall =
  Print_syntax.show_raw_id_name := show_raw_id_name;
  
  let program, automaton = Parse.parse_file file in
  let automaton =
    match automaton with
    | Some a -> a
    | None -> assert false in

  let () =
    print_endline @@ Raw_program.show_raw_program program;
    let (env, (initial_state, trans), priority) = automaton in
    print_endline "env:";
    (match env with
    | Some env -> print_endline @@ show_itype_env env
    | None -> print_endline "None");
    print_endline "initial:"; print_endline @@ show_state initial_state;
    print_endline "transition:"; print_endline (List.map show_transition_rule trans |> String.concat "\n");
    print_endline "priority:"; print_endline (List.map show_priority_rule priority |> String.concat "\n")
  in
  
  let program' = Trans_raw_program.convert_all program in
  let () =
    print_endline "program:"; print_endline @@ Print_syntax.show_program program'; print_endline ""
  in
  
  Check.check_input program' automaton;
  
  let (env, (initial_state, transition), priority) = automaton in
  let all_states = List.map fst priority in
  let max_m = List.fold_left (fun a (_, b) -> if a < b then b else a) (-1) priority in
  let env =
    match always_use_canonical_type_env, env with
    | true, _ | _, None ->
      print_endline "INFO: using the canonical intersection type environment";
      canonical_it_program program' all_states max_m
    | _, Some env ->
      print_endline "INFO: using the given intersection type environemnt";
      set_id_on_env env program'
    in
  print_endline "env:"; print_endline @@ show_itype_env env;
  
  let func_priority = get_priority env in
  let program_ = trans_program env program' (as_multi_function transition) (as_function priority) initial_state all_states in
  
  print_endline "program (after):";
  print_endline @@ Print_syntax.show_program_as_ocaml program_;
  
  let () =
    let oc = open_out "tmp.ml" in
    let fmt = Format.formatter_of_out_channel oc in
    Format.fprintf fmt "%s" (Print_syntax.show_program_as_ocaml program_);
    close_out oc in
  
  let hflz = Trans_program.to_hflz program_ func_priority encode_nondet_with_forall in
  
  Format.printf "%a" Hflmc2_syntax.Print.(hflz_hes simple_ty_) hflz; Format.print_flush ();
  Manipulate.Hflz_typecheck.type_check hflz;
  Format.printf "%a" Hflmc2_syntax.Print.(hflz_hes simple_ty_) hflz; Format.print_flush ();
  Format.print_string "\n=======\n"; Format.print_flush ();
  
  let hflz = Manipulate.Hes_optimizer.eliminate_unreachable_predicates hflz in
  Manipulate.Hflz_typecheck.type_check hflz;
  
  Format.printf "%a" Hflmc2_syntax.Print.(hflz_hes simple_ty_) hflz; Format.print_cut (); Format.print_flush ();
  print_endline @@ show_priority func_priority;
  
  hflz, func_priority

let eliminate_unused_argument = Eliminate_unused_argument.eliminate_unused_argument
let infer_type = Type_hflz.infer_type
let abbrev_variable_names = Eliminate_unused_argument_util.abbrev_variable_names