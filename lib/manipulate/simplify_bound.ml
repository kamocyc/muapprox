open Hflmc2_syntax
open Hflz

let string_of_id id =  
  let replace_apos s =
    s
    |> Str.global_replace (Str.regexp "'") "_ap_"
    |> Str.global_replace (Str.regexp "!") "_exc_"
    |> Str.global_replace (Str.regexp "#") "_sha_"
  in
  Id.to_string id
  |> replace_apos
 
let convert_to_smt2 (exprs : 'a t list) =
  let used_variables = ref [] in
  let trans_op op = match op with
    | Arith.Add -> "+"
    | Sub -> "-"
    | Mult -> "*"
    | Div | Mod -> failwith "trans_op: unsupported operator"
  in
  let rec trans_arith a1 = match a1 with
    | Arith.Int i -> string_of_int i
    | Var v ->
      used_variables := v :: !used_variables;
      (* with id *)
      string_of_id v
    | Op (op, [a1; a2]) -> "(" ^ trans_op op ^ " " ^ trans_arith a1 ^ " " ^ trans_arith a2 ^ ")"
    | Op _ -> failwith "trans_arith"
  in
  let trans_pred op = match op with
    | Formula.Eq -> "="
    | Le -> "<="
    | Ge -> ">="
    | Lt -> "<"
    | Gt -> ">"
    | Neq -> failwith "trans_pred: Neq" in
  let trans_pred_ op a1 a2 =
    if op = Formula.Neq then
      None
    else
      Some ("(" ^ trans_pred op ^ " " ^ trans_arith a1 ^ " " ^ trans_arith a2 ^ ")")
  in
  let preds, not_useds =
    List.map
      (fun e ->
        match e with
        | Pred (op, [a1; a2]) -> begin
          match trans_pred_ op a1 a2 with
          | None -> false, e, ""
          | Some s -> true, e, s
        end
        | _ -> failwith "convert_to_smt2")
      exprs
    |> List.partition (fun (b, _, _) -> b)
  in
  let not_useds = List.map (fun (_, e, _) -> e) not_useds in
  match preds with
  | [] -> None, [], not_useds
  | preds -> begin
    let body = "(or\n" ^ (List.map (fun (_, _, s) -> "  " ^ s ^ "") preds |> String.concat "\n") ^ ")" in
    let variables = Hflmc2_util.remove_duplicates (=) !used_variables in
    Some ((variables
    |> List.map string_of_id
    |> List.map (fun v -> "(declare-const " ^ v ^ " Int)\n")
    |> String.concat "") ^ "\n" ^
    "(assert " ^ body ^ ")\n(apply (then ctx-solver-simplify ctx-solver-simplify simplify))\n"),
    variables,
    not_useds
  end

let parse_sexp s =
  let open Core in
  match Sexplib.Sexp.parse s with
  | Done (model, _) -> begin
    match model with
    | List [Atom "goals"; List (Atom "goal"::xs)] -> begin
      let xs = List.filter ~f:(fun x -> match x with
        | (Atom _) -> false
        | _ -> true
      ) xs in
      let body = 
        match xs with
        | [] -> Sexp.Atom "true"
        | [x] -> x
        | xs -> List (Atom "and"::xs) in
      body
    end
    | _ -> failwith @@ "simplify_body: " ^ Sexp.to_string model
  end
  | _ -> failwith "failed to parse model (2)" 

let to_op s = match s with
  | "+" -> Arith.Add
  | "-" -> Arith.Sub
  | "*" -> Arith.Mult
  | _ -> failwith "to_op"

let to_predicate s = match s with
  | "<=" -> Formula.Le
  | ">=" -> Formula.Ge
  | "<" -> Formula.Lt
  | ">" -> Formula.Gt
  | "=" -> Formula.Eq
  | "<>" -> Formula.Neq
  | _ -> failwith @@ "to_predicate: " ^ s

let rec to_ors ors = match ors with
  | [x] -> x
  | x::xs -> Or (x, to_ors xs)
  | _ -> failwith "to_ors"
  
let flip_pred = function
  | Formula.Eq -> Formula.Eq
  | Neq -> Neq
  | Le -> Ge
  | Ge -> Le
  | Lt -> Gt
  | Gt -> Lt  
  
let to_hflz const_bounds variables parsed =
  let open Core in
  print_endline "sexp";
  print_endline @@ Sexp.to_string parsed;
  let get_const_clauses clauses =
    let consts =
      List.filter_map
        ~f:(fun clause -> match clause with
          | Pred (op, [e1; e2]) -> begin
            match op, e1, e2 with
            | Lt, Var v, Int i -> Some (v, i)
            | _ -> None
          end
          | _ -> assert false
        )
        clauses in
    (* 存在しない OR 存在するがboundが元よりも小さい 場合に元の定数項を追加 *)
    List.filter_map
      ~f:(fun (v, i) ->
        match List.find ~f:(fun (v', i') -> Id.eq v v' && i' >= i) consts with
        | None -> Some (v, i)
        | Some _ -> None
      )
      const_bounds
    |>
    List.map
      ~f:(fun (v, i) -> Pred (Lt, [Var v; Int i]))
  in
  let get_var_id x =
    match List.filter ~f:(fun id -> String.(=) (string_of_id id) x) variables with
    | [x] -> x
    | [] -> failwith @@ "get_var_id: not found (" ^ x ^ ")"
    | _ -> failwith @@ "get_var_id: many found (" ^ x ^ ")" in
  let rec go_arith xs = match xs with
    | Sexp.List ((Atom op)::args) -> begin
      let op = to_op op in
      match op, List.map ~f:go_arith args with
      | Arith.Sub, [Arith.Int i] -> Int (-i)
      | Arith.Sub, [x] -> Arith.Op (Sub, [Int 0; x])
      | _ -> begin
        assert (List.length args = 2);
        Arith.Op (op, List.map ~f:go_arith args)
      end
    end
    | Atom i -> begin
      let expr =
        try
          Arith.Int (int_of_string i)
        with _ ->
          Var (get_var_id i)
        in
      expr
    end
    | _ -> failwith "go_arith"
  in
  let convert_rhs x = match x with
    | Sexp.List (Atom "+"::x1::[Atom x2]) -> begin
      let constant =
        match x1 with
        | List (Atom "-"::[Atom i]) ->
          Some (0 - (int_of_string i))
        | Atom i ->
          Some (int_of_string i)
        | _ -> None
      in
      match constant with
      | Some c -> c, Arith.Var (get_var_id x2)
      | None -> 0, go_arith x 
    end
    | _ -> begin
      0, go_arith x
    end
  in
  let add_const x1 c =
    let c = -c in
    if c = 0 then x1
    else (
      match x1 with
      | Sexp.Atom _ -> Sexp.List ((Atom "+")::x1::[Atom (string_of_int c)])
      | Sexp.List ((Atom op)::args) -> begin
        match op with
        | "*" | "-" -> Sexp.List ((Atom "+")::x1::[Atom (string_of_int c)])
        | "+" -> begin
          let added = ref false in
          let args =
            List.map ~f:(fun arg -> match arg with
              | Atom i -> begin
                if not !added then
                  try
                    let i = int_of_string i in
                    added := true;
                    Sexp.Atom (string_of_int (i + c))
                  with _ -> arg
                else arg
              end
              | List _ -> arg
            ) args in
          Sexp.List ((Atom op)::args)
        end
        | _ -> failwith "add_const: illegal operator"
      end
      | _ -> failwith "add_const: unexpected sexp"
    )
  in
  (* <= を <にする変換 *)
  let go_pred parsed =
    let pred, lhs, rhs =
      match parsed with
      | Sexp.List ((Atom "not")::[List ((Atom pred)::x1::[x2])]) -> begin
        let pred = to_predicate pred |> Formula.negate_pred in
        let x2_const, x2_term = convert_rhs x2 in
        let x1 = add_const x1 x2_const in
        pred, go_arith x1, x2_term
      end
      | Sexp.List ((Atom pred)::x1::[x2]) ->
        let pred = to_predicate pred in
        pred, go_arith x1, go_arith x2
      | _ -> failwith "go_pred" in
    let pred = flip_pred pred in
    Pred (pred, [rhs; lhs])
  in
  let go_ors parsed = match parsed with
    | Sexp.List (op::args) -> begin
      let clauses =
        match op with
        | (Atom "or") -> begin
          (List.map ~f:go_pred args)
          |> Hflmc2_util.remove_duplicates (Stdlib.(=))
        end
        | _ -> [go_pred parsed]
      in
      let clauses = clauses @ get_const_clauses clauses in
      clauses
    end
    | _ -> failwith "illegal operator (2)"
  in
  go_ors parsed

let get_const_bound exprs =
  let rec go = function
    | Pred (Lt, [Var v; Int i])::xs -> (v, i)::(go xs)
    | Pred (Lt, [_; _])::xs -> go xs
    | _::xs -> go xs
    | [] -> []
  in
  go exprs
  
let simplify_bound_with_z3 (exprs : 'a t list) =
  let const_bounds = get_const_bound exprs in
  let buf, variables, not_useds = convert_to_smt2 exprs in
  match buf with
  | None -> exprs
  | Some buf -> begin
    let get_random_file_name () = Printf.sprintf "/tmp/%d.tmp" (Random.self_init (); Random.int 0x10000000) in
    let file_name = get_random_file_name () in
    print_endline "simplify_bound_with_z3";
    print_endline "input file_name";
    print_endline file_name;
    Hflmc2_util.write_file file_name buf;
    let output_path = get_random_file_name () in
    ignore @@ Unix.system @@ "z3 " ^ file_name ^ " pp.max_depth=10000 pp.min-alias-size=10000 > " ^ output_path;
    print_endline "output file_name";
    print_endline output_path;
    let s = Hflmc2_util.read_file output_path in
    let parsed = parse_sexp s in
    let exprs = to_hflz const_bounds variables parsed in
    (* print_endline (Hflmc2_util.show_list Hflz_util.show_hflz exprs); *)
    print_endline (Hflmc2_util.show_list Print_syntax.show_hflz exprs);
    print_endline "";
    exprs @ not_useds
  end
  