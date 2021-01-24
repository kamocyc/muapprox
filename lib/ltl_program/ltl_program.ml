open Program
open Itype
open Trans

let print_location lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "file: %s, line %d, column %d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
(* 
let transition_function1 q symbol =
  match q with
  | ITFunc _ -> failwith "a"
  | ITState s ->begin
    match s, symbol with
    | _, "a" -> [ITState "qa"]
    | _, "b" -> [ITState "qb"]
    | _ -> failwith "transition_function1"
  end

let priority q = 
  match q with
  | ITFunc _ -> failwith "a"
  | ITState s ->begin
    match s with
    | "qa" -> 0
    | "qb" -> 1
    | _ -> failwith "priority"
  end *)

let as_function assoc key =
  List.assoc key assoc
  
let as_multi_function assoc key =
  match List.find_all (fun (k, v) -> key = k) assoc with
  | [] -> failwith @@ "as_multi_function (key=(" ^ fst key ^ ", " ^ snd key ^ "))"
  | l -> l |> List.map (fun (k, v) -> v)
  
let domain file =
  Core.In_channel.with_file file ~f:begin fun ch ->
    let lexbuf = Lexing.from_channel ch in
    let program, env =
      try
        Parser.main Lexer.token lexbuf
      with
      | Parser.Error as b->
        print_string "Parse rrror: ";
        print_endline @@ print_location lexbuf;
        raise b
        in
    print_endline @@ Raw_program.show_hes program;
    (match env with
    | Some (env, initial_state, trans, priority) -> begin
      print_endline "env:";
      print_endline @@ show_itype_env env;
      print_endline "initial:";
      print_endline initial_state;
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
      let func_priority = get_priority env in
      let program_ = trans_hes env program' (as_multi_function transition) (as_function priority) initial_state in
      print_endline "program (after):";
      print_endline @@ show_hes program_;
      print_endline "Omega:";
      print_endline (List.map (fun (f, p) -> f ^ " -> " ^ string_of_int p) func_priority |> String.concat "\n");
      print_endline ""
    end
    | None -> failwith "a"
  end
