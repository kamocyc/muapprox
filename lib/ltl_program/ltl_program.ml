open Program
open Itype
open Trans

let print_location lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "file: %s, line %d, column %d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let as_function assoc key =
  match List.find_opt (fun (k, s) -> k = key) assoc with
  | None -> failwith @@ "as_function: Not_found (key=" ^ show_state key ^ ")"
  | Some (_, s) -> s

let as_multi_function assoc key =
  match List.find_all (fun (k, v) -> k = key) assoc with
  | [] -> failwith @@ "as_multi_function (key=(" ^ show_state (fst key) ^ ", " ^ show_symbol (snd key) ^ "))"
  | l -> l |> List.map (fun (k, v) -> v)

let convert_ltl file =
  Core.In_channel.with_file file ~f:begin fun ch ->
    let lexbuf = Lexing.from_channel ch in
    let program, env =
      try
        Parser.main Lexer.token lexbuf
      with
      | Parser.Error as b->
        print_string "Parse error: ";
        print_endline @@ print_location lexbuf;
        raise b
        in
    print_endline @@ Raw_program.show_hes program;
    (match env with
    | Some (env, initial_state, trans, priority) -> begin
      print_endline "env:";
      print_endline @@ show_itype_env env;
      print_endline "initial:";
      print_endline @@ show_state initial_state;
      print_endline "transition:";
      print_endline (List.map show_transition_rule trans |> String.concat "\n");
      print_endline "priority:";
      print_endline (List.map show_priority_rule priority |> String.concat "\n");
    end
    | None -> ());
    let program' = convert_all program in
    print_endline "program:";
    print_endline @@ show_hes program';
    print_endline "";
    match env with
    | Some (env, initial_state, transition, priority) -> begin
      let all_states = List.map fst priority in
      let max_m = List.fold_left (fun a (_, b) -> if a < b then b else a) (-1) priority in
      let env = canonical_it_hes program' all_states max_m in
      print_endline "env:";
      print_endline @@ show_itype_env env;
      (* let env = env in *)
      let func_priority = get_priority env in
      let program_ = trans_hes env program' (as_multi_function transition) (as_function priority) initial_state all_states in
      (* print_endline "program (after):";
      print_endline @@ show_hes_as_ocaml program_ *)
      let hflz = to_hflz program_ func_priority in
      Manipulate.Hflz_typecheck.type_check hflz;
      Format.printf "%a" Hflmc2_syntax.Print.(hflz_hes simple_ty_) hflz;
      Format.print_flush ();
      Format.print_string "\n=======\n";
      Format.print_flush ();
      let hflz = Manipulate.Hes_optimizer.eliminate_unreachable_predicates hflz in
      let hflz = Manipulate.Hes_optimizer.simplify hflz in
      Manipulate.Hflz_typecheck.type_check hflz;
      Format.printf "%a" Hflmc2_syntax.Print.(hflz_hes simple_ty_) hflz;
      (* print_endline "Omega:";
      print_endline (List.map (fun (f, p) -> f ^ " -> " ^ string_of_int p) func_priority |> String.concat "\n");
      print_endline "" *)
    end
    | None -> failwith "a"
  end
