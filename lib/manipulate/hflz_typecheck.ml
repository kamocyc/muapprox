module Hflz = Hflmc2_syntax.Hflz
module Id = Hflmc2_syntax.Id
module Type = Hflmc2_syntax.Type
module Arith = Hflmc2_syntax.Arith
open Hflz

type ty_env = (Type.simple_ty Type.arg Id.t) list

let log_src = Logs.Src.create "Typecheck"
module Log = (val Logs.src_log @@ log_src)

let log_string = Hflz_util.log_string Log.app

let ensure_all_variable_ids_are_unique_expr env seen_ids (phi : 'a Hflz.t) =
  let rec go env (phi : 'a Hflz.t) = match phi with
    | Var v -> begin  
      match List.find_opt (Id.eq @@ Hflz_util.lift_id v) env with
      | Some _ -> ()
      | None -> assert false 
    end
    | Abs (x, p) -> begin
      if Hashtbl.mem seen_ids x.id then failwith @@ "duplicated id: " ^ Id.to_string x;
      Hashtbl.add seen_ids x.id x;
      go (x::env) p
    end
    | Forall (x, p) -> begin
      if Hashtbl.mem seen_ids x.id then failwith @@ "duplicated id: " ^ Id.to_string x;
      Hashtbl.add seen_ids x.id x;
      go (x::env) p
    end
    | Exists (x, p) -> begin
      if Hashtbl.mem seen_ids x.id then failwith @@ "duplicated id: " ^ Id.to_string x;
      Hashtbl.add seen_ids x.id x;
      go (x::env) p
    end
    | Bool _ -> ()
    | Or (p1, p2) -> (go env p1; go env p2)
    | And (p1, p2) -> (go env p1; go env p2)
    | App (p1, p2) -> (go env p1; go env p2)
    | Arith a -> go_arith env a
    | Pred (_, a) -> List.iter (go_arith env) a
  and go_arith env (a : Arith.t) = match a with
    | Int _ -> ()
    | Var v -> begin
      match List.find_opt (Id.eq @@ {v with ty=Type.TyInt}) env with
      | Some _ -> ()
      | None -> assert false 
    end
    | Op (_, a) -> List.iter (go_arith env) a
  in
  go env phi

let ensure_all_variable_ids_are_unique (hes : 'a hes) =
  let seen_ids = Hashtbl.create 100 in
  let (entry, rules) = hes in
  let env =
    List.map
      (fun {var; _} ->
        Hashtbl.add seen_ids var.id (Hflz_util.lift_id var);
        Hflz_util.lift_id var
      )
      rules in
  ensure_all_variable_ids_are_unique_expr env seen_ids entry;
  Hashtbl.reset seen_ids; (* 同じスコープでIDの重複があったらエラー *)
  List.iter
    (fun {body; _} ->
      ensure_all_variable_ids_are_unique_expr env seen_ids body;
      Hashtbl.reset seen_ids (* 同じスコープでIDの重複があったらエラー *)
    )
    rules

let type_check_arith : ty_env -> Arith.t -> bool = fun env arith ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_id = Id.show Fmt.nop in
  let rec go = fun arith -> match arith with
  | Arith.Int _ -> true
  | Arith.Var v -> begin
    match List.find_opt (fun k -> Id.eq k v) env with
    | Some {Id.ty=ty'; _} ->
      if ty' = Type.TyInt
      then true
      else failwith @@ "[Arith] var `" ^ show_id v ^ "`'s type should be Int, but actual: " ^ show_arg ty' ^ "."
    | None -> failwith @@ "[Arith] unbound var `" ^ show_id v ^ "`' "
  end
  | Arith.Op (_, args) ->
    List.length args = 2 &&
    List.for_all go args in
  go arith

let get_hflz_type : ty_env -> Type.simple_ty Hflz.t -> Type.simple_ty = fun env hfl ->
  let show_arg_ty = fun fmt ty -> Format.pp_print_string fmt @@ Type.show_ty Fmt.nop ty in
  let show_arg = Type.show_arg show_arg_ty in
  let show_arg_ty_s = fun ty -> Hflmc2_util.fmt_string Hflmc2_syntax.Print.simple_argty ~margin:200 ty in
  let show_id = Id.show Fmt.nop in
  let show_formula f = 
    let buf = Buffer.create 100 in
    let fmt = Format.formatter_of_buffer buf in
    Print_syntax.hflz Print_syntax.simple_ty_ fmt f;
    Format.pp_print_flush fmt ();
    Buffer.contents buf 
  in
  let show_fm f =
    " (formula: " ^ (show_formula f) ^ ")"
  in
  let rec go : ty_env -> Type.simple_ty Hflz.t -> Type.simple_ty = fun env hfl -> match hfl with
  | Bool _ -> Type.TyBool ()
  | Var ({ty;_} as v) -> begin
    (* 環境に出現していることをチェック *)
    (* ここで出ているVarは、Int型ではない。Int型変数はArith内に出る *)
    match List.find_opt (fun k -> Id.eq k v) env with
    | Some {ty=ty';_} -> 
      if Type.TySigma ty = ty'
      then ty
      else
        failwith @@
          "Var: `" ^ (show_id v) ^ "` type mismatch:\n" ^
          "type of variable in formula:\n" ^
          Hflmc2_util.fmt_string Print_syntax.simple_ty ty ^
          " / type in environment:\n" ^
          Hflmc2_util.fmt_string (Hflmc2_syntax.Print.argty Print_syntax.simple_ty) ty' ^
          ") (type of variable in formula: " ^ (show_arg @@ Type.TySigma ty) ^
          " / type in environment: " ^ (show_arg ty')  ^ ")"
    | None -> failwith @@ "Var: unbound variable (" ^ (show_id v) ^ ")"
  end
  | Or (f1, f2) -> begin
    if go env f1 = Type.TyBool () && go env f2 = Type.TyBool ()
    then Type.TyBool ()
    else failwith @@ "Or: both formulae should be bool type (left: " ^ (show_fm f1) ^ ", right: " ^ (show_fm f2) ^ ")"
  end
  | And (f1, f2) -> begin
    if go env f1 = Type.TyBool () && go env f2 = Type.TyBool ()
    then Type.TyBool ()
    else failwith @@ "And: both formulae should be bool type (left: " ^ (show_fm f1) ^ ", right: " ^ (show_fm f2) ^ ")"
  end
  | Abs (arg, body) -> begin
    Type.TyArrow (arg, go (arg::env) body)
  end
  | Forall (arg, body) -> go (arg::env) body
  | Exists (arg, body) -> go (arg::env) body
  | App (f1, f2) -> begin
    let ty1 = go env f1 in
    match ty1 with
    (* 唯一subformulaにIntが許される *)
    | TyArrow ({ty=TyInt; _}, tybody) -> begin
      match f2 with
        | Arith arith -> 
          if type_check_arith env arith
          then tybody
          else assert false
        | _ -> failwith @@ "App: f2 should be arithmetic expression" ^ (show_fm hfl)
    end
    | TyArrow ({ty=TySigma ty; _} as arg, tybody) -> begin
      let ty2 = go env f2 in
      if Type.eq_modulo_arg_ids ty2 ty
      then tybody
      else failwith @@ "App_TyArrow type mismatch" ^ (show_fm hfl) ^ "ty1=" ^ (show_arg arg.ty) ^ " / ty2=" ^ (show_arg (TySigma ty2)) ^
        "\nsimplified:\nty1=" ^ (show_arg_ty_s arg.ty) ^ "/ ty2=" ^ (show_arg_ty_s (TySigma ty2))
    end
    | TyBool _ -> failwith @@ "App: left-hand term should not be boolean. (left-hand term=" ^ (show_fm f1) ^ ", right-hand term=" ^ (show_fm f2) ^ ")"
  end
  | Pred (_, args) -> begin
    List.iter (fun arg -> if type_check_arith env arg then () else assert false) args;
    let arg_num = List.length args in
    if arg_num <> 2 then assert false;
    Type.TyBool ()
  end
  | Arith _ -> failwith @@ "Illegal Arith: " ^ (show_fm hfl) in
  go env hfl

let get_duplicates cmp ls =
  List.filter_map
    (fun var ->
      match List.filter (fun var' -> cmp var' var) ls with
      | [_] -> None
      | (x::_) as xs ->
        Some (x, List.length xs)
      | [] -> assert false
    )
    ls

let set_variable_ty (hes : Type.simple_ty hes) : Type.simple_ty hes =
  let show_id = Id.show Fmt.nop in
  let (entry, rules) = hes in
  let env = List.map (fun {var;_} -> var) rules in
  let rec go env phi = match phi with
    | Var v -> begin
      match List.find_opt (fun k -> Id.eq k v) env with
      | Some {ty=ty';_} ->
        if not @@ Type.eq_modulo_arg_ids v.ty ty' then
          failwith @@
            "Var: `" ^ (show_id v) ^ "`type mismatch (eq_modulo_arg_ids):\n" ^
            "type of variable in formula:\n" ^
            Hflmc2_util.fmt_string Print_syntax.simple_ty v.ty ^
            " / type in environment:\n" ^
            Hflmc2_util.fmt_string Print_syntax.simple_ty ty';
        Var {v with ty=ty'}
      | None -> failwith @@ "Var: unbound variable (" ^ (show_id v) ^ ")"
    end
    | Bool b -> Bool b
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | And (p1, p2) -> And (go env p1, go env p2)
    | Abs (x, p) -> begin
      let env =
        match x.ty with
        | Type.TySigma ty ->
          {x with ty=ty} :: env
        | _ -> env
      in
      Abs (x, go env p)
    end
    | Forall (x, p) -> Forall (x, go env p)
    | Exists (x, p) -> Exists (x, go env p)
    | App (p1, p2) -> App (go env p1, go env p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  let entry = go env entry in
  let rules =
    List.map
      (fun {var; body; fix} ->
        let body = go env body in
        {var; body; fix}
      )
      rules in
  (entry, rules)

let type_check (hes : Type.simple_ty hes) : unit =
  let path = Print_syntax.MachineReadable.save_hes_to_file true hes in
  log_string @@ "Not checked HES path: " ^ path;
  (* let path = Print_syntax.FptProverHes.save_hes_to_file hes in
  log_string @@ "Not checked HES path (.hes): " ^ path; *)
  let show_ty = Type.show_ty Fmt.nop in
  let (entry, rules) = hes in
  let env = List.map (fun {var={ty;_} as var;_} -> {var with ty=Type.TySigma ty}) rules in
  let () =
    let pred_count = get_duplicates (fun a b -> a.Id.name = b.Id.name) env in
    match pred_count with
    | [] -> ()
    | xs -> failwith @@ "duplicated predicates (comparing only names of predicates) (" ^ (List.map (fun (var, _) -> Id.to_string var) xs |> String.concat ", ") ^ ")" in
  let () =
    List.iter
      (fun {body; var; _} ->
        let rec f = function
          | Abs (x, b) -> x :: (f b)
          | _ -> [] in
        let args = f body in
        (* print_endline "args:";
        print_endline (List.map (fun var -> var.Id.name) args |> String.concat ", "); *)
        let counts = get_duplicates (fun a b -> a.Id.name = b.Id.name) args in
        (* print_endline "counts:";
        print_endline (List.map (fun (var, i) -> var.Id.name ^ ":" ^ string_of_int i) counts |> String.concat ", "); *)
        match counts with
        | [] -> ()
        | xs -> failwith @@ "duplicated arguments (comparing only names of predicates) (predicate: " ^ Id.to_string var ^ ", args: " ^ (List.map (fun (var, _) -> Id.to_string var) xs |> String.concat ", ") ^ ")"
      )
      rules in
  let ty' = get_hflz_type env entry in
  if not @@ Type.eq_modulo_arg_ids ty' (TyBool ()) then failwith @@ "rule type mismatch (Checked type: " ^ show_ty ty' ^ " / Env type: " ^ show_ty (TyBool ()) ^ ")";
  List.iter (fun ({var={ty;_}; body; _}) -> 
    let ty' = get_hflz_type env body in
    if not @@ Type.eq_modulo_arg_ids ty' ty then failwith @@ "rule type mismatch (Checked type: " ^ show_ty ty' ^ " / Env type: " ^ show_ty ty ^ ")"
  ) rules;
(*   
  (* 近似処理で同じIDの変数が現れる *)
  print_endline @@ Print_syntax.show_hes (merge_entry_rule hes);
  ensure_all_variable_ids_are_unique hes; *)
  ()

let ensure_no_shadowing_expr (env : ty_env) (phi : 'a Hflz.t) : 'a Type.arg Id.t list =
  let rec go env phi = 
    let get_duplicates x =
      match List.find_opt (fun x' -> x.Id.name = x'.Id.name) env with
      | Some x' -> [x']
      | None -> []
    in
    match phi with
    | Var _ -> []
    | Arith _ -> []
    | Bool _ -> []
    | Pred _ -> []
    | Abs (x, p) -> begin
      (go (x::env) p) @ (get_duplicates x)
    end
    | Forall (x, p) -> 
      (go (x::env) p) @ (get_duplicates x)
    | Exists (x, p) -> 
      (go (x::env) p) @ (get_duplicates x)
    | App (p1, p2) ->
      go env p1 @ go env p2
    | And (p1, p2) ->
      go env p1 @ go env p2
    | Or (p1, p2) ->
      go env p1 @ go env p2
    in
  go env phi

(* shadowning is normally harmless *)
let ensure_no_shadowing (hes : Type.simple_ty hes) : unit =
  let (entry, rules) = hes in
  let env = List.map (fun {var={ty;_} as var;_} -> {var with ty=Type.TySigma ty}) rules in
  let () =
    let pred_count = get_duplicates (fun a b -> a.Id.name = b.Id.name) env in
    match pred_count with
    | [] -> ()
    | xs -> failwith @@ "duplicated predicates (comparing only names of predicates) (" ^ (List.map (fun (var, _) -> Id.to_string var) xs |> String.concat ", ") ^ ")" in
  let dups =
    (ensure_no_shadowing_expr env entry) @
    (List.map (fun {body; _} -> ensure_no_shadowing_expr env body) rules |> List.flatten) in
  match dups with
  | [] -> ()
  | dups -> failwith @@ "shadowed variables: (" ^ (List.map (fun var -> var.Id.name) dups |> String.concat ", ") ^ ")"
