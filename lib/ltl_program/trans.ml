open Itype
open Program

module Program2 = Program

let upto m =
  let rec go m = if m = 0 then [0] else m :: (go (m - 1)) in    
  go m

(* simple typeに対するcanonical intersection typeを返す *)
let canonical_it (simple_type : Type.simple_ty) states max_m =
  let product xs ys =
    List.map (fun x -> List.map (fun y -> (x, y)) ys) xs |> List.flatten in
  let ms = upto max_m in
  let rec go simple_type = match simple_type with
    | Type.TyUnit () -> states |> List.map (fun s -> ITState s)
    | Type.TyArrow ({ty=Type.TyInt; _}, body) -> go body |> List.map (fun ty -> ITFunc (IAInt, ty))
    | Type.TyArrow ({ty=Type.TySigma t1; _}, t2) ->
      go t2 |>
      List.map (fun t2 ->
        let args = product (go t1) ms in
        ITFunc (IAInter args, t2)
      ) in
  go simple_type

(* プログラムのcanonical intersection type を返す 
  （各関数のsimple typeをcanonical intersection typeにする） *)
let canonical_it_hes (h : hes) (states : string list) (max_m : int) =
  let ms = upto max_m in
  let to_funty args =
    let rec go args = match args with
      | [] -> Type.TyUnit ()
      | x::xs -> Type.TyArrow ({ty=x; name=""; id=0}, go xs) in
    go args in
  let program, hes = h in
  let hes_ty = List.map (fun {args; var; _} ->
    canonical_it (to_funty (List.map (fun (_, t) -> t) args)) states max_m |>
      List.map (fun s ->
        List.map (fun mm -> 
          (var, (s, mm))
        ) ms
      ) |> List.flatten
  ) hes |> List.flatten in
  hes_ty
  
let max_env (env : itenv) (m : int): itenv =
  env |>
  List.map (function
    | v, ITEInt -> v, ITEInt
    | v, ITEInter (t, m1, m2) -> v, ITEInter (t, m1, max m2 m))

let lookup_with_itype_base env x ty f n =
  match List.filter_map f env with
  | [] -> failwith @@ "lookup_with_itype_base: not found (var=" ^ x ^ ", ty=" ^ show_itype ty ^ ", from=" ^ n ^ ")"
  | xs -> begin
    let m' = List.fold_left (fun max (_, _, m') -> if max < m' then m' else max) (-1) xs in
    match List.filter (fun (_, m, m') -> m = m') xs with
    | [] -> failwith @@ "lookup_with_itype_base: max priority mismatch (var=" ^ x ^ ", ty=" ^ show_itype ty ^ ", max=" ^ string_of_int m' ^ ", priorities=" ^ (List.map (fun (_, m, _) -> string_of_int m) xs |> String.concat ", ") ^ ", from=" ^ n ^ ")"
    | [(ty, m, _)] -> Some (ty, m)
    | _ -> failwith "lookup_with_itype_base: false"
  end
 
let lookup_with_itype env x ty =
  lookup_with_itype_base env x ty (fun (id, ty') ->
    if id = x then begin
      match ty' with
      | ITEInter (t, m, m') -> if t = ty then Some (t, m, m') else None
      | ITEInt -> None
    end else None
  ) "var"

let lookup_arg_type_by_body_type env x ty =
  lookup_with_itype_base env x ty (fun (id, ty') ->
    if id = x then begin
      match ty' with
      | ITEInter ((ITFunc (_, body)) as t, m, m') -> if body = ty then Some (t, m, m') else None
      | _ -> None
    end else None
  ) "fun_body"
  |> Option.map (fun (t, m) -> match t with ITFunc (arg, body) -> (arg, body) | _ -> assert false)

let make_var_name (x : string) (v : itype) (m : int) =
  x ^ "_{" ^ show_itype v ^ "," ^ string_of_int m ^"}"

let make_nondet terms = 
  let rec go : Program2.program list -> Program2.program = function 
    | [] -> failwith "make_nondet"
    | [x1] -> x1
    | [x1; x2] -> PNonDet (x1, x2)
    | x::xs -> PNonDet(x, go xs) in
  go terms
    
let intersect l1 l2 =
  let comp = (=) in
  l2 |> List.filter (fun e -> List.exists (comp e) l1)

let decompose_ty ty = match ty with
  | ITFunc (arg, body) -> begin 
    match arg with
    | IAInt -> failwith "decompose_ty"
    | IAInter tys -> tys, body
  end
  | _ -> failwith "decompose_ty2"
  
let decompose_ty_int ty = match ty with
  | ITFunc (arg, body) -> begin 
    match arg with
    | IAInter tys -> failwith "decompose_ty_int"
    | IAInt -> body
  end
  | _ -> failwith "decompose_ty_int2"

type stenv = (string * Type.simple_ty) list

let decompose_itype' ty = match ty with
  | ITFunc' (a, b) -> a, b
  | _ -> failwith "decompose_itype'"

let rec to_itype' e = match e with
  | ITState s -> ITState' s
  | ITFunc (arg, body) -> ITFunc' (arg, to_itype' body)
let to_itype'_from_envtype e = match e with
  | ITEInt -> ITInt'
  | ITEInter (t, _, _) -> to_itype' t
let rec from_itype' e = match e with
  | ITState' s -> ITState s
  | ITFunc' (a, b) -> ITFunc (a, from_itype' b)
  | ITInt' -> failwith "from_itype'"

let get_arg_type (env : itenv) term states =
  let states = List.map (fun s -> ITState' s) states in
  let rec go (env : itenv) term : itype' list = match term with
    | PUnit -> states
    | PVar var -> begin
      match List.find_all (fun (id, _) -> id = var) env |> List.map (fun (_, v) -> v) with
      | [] -> failwith "unbounded"
      | ty -> List.map to_itype'_from_envtype ty |> List.sort_uniq compare
    end
    | PApp (p1, p2) -> begin
      let tys1 = go env p1 in
      let tys2 = go env p2 in
      List.map
        (fun ty1 ->
          let argty, bodyty = decompose_itype' ty1 in
          assert (
            match argty with
            | IAInter tys -> begin
              List.mapi (fun i (ty1, _) -> to_itype' ty1 = List.nth tys2 i) tys |>
              List.for_all (fun x -> x)
            end
            | _ -> false);
          bodyty
        )
        tys1
    end
    | PAppInt (p1, p2) -> begin
      let tys1 = go env p1 in
      List.map
        (fun ty1 ->
          let argty, bodyty = decompose_itype' ty1 in
          assert (
            match argty with
            | IAInter _ -> false
            | IAInt -> true);
          bodyty
        )
        tys1
    end
    | PIf (_, p1, p2) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      assert (ty1 = ty2);
      ty1
    end
    | PNonDet (p1, p2) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      assert (ty1 = ty2);
      ty1
    end
    | PEvent (e, p1) -> go env p1
    in
  go env term
  
let make_app v xs =
  let rec go (xs: Program2.program list): Program2.program = match xs with
    | [] -> v
    | x::xs -> PApp (go xs, x) in
  go (List.rev xs)

let trans (env : itenv) (term : program) transition_function priority all_states =
  let transition_function ty ev = match ty with
    | ITFunc  _ -> failwith "transition_function"
    | ITState s -> transition_function (s, ev) |> List.map (fun s -> ITState s)
  in
  let priority ty = match ty with
    | ITFunc _ -> failwith "priority"
    | ITState s -> priority s
  in
  let rec go_prog (env : itenv) (term : program) (ty : itype): Program2.program = (* print_endline @@ "go_prog:" ^ show_program term; *) match term with
    | PUnit -> PUnit
    | PVar x -> begin
      match lookup_with_itype env x ty with
      | None -> failwith @@ "PVar: not found (" ^ x ^ ": (" ^ show_itype ty ^ ", " ^ string_of_int 0 ^ ")"
      | Some (v, m) -> PVar (make_var_name x v m)
    end
    | PNonDet (p1, p2) -> PNonDet (go_prog env p1 ty, go_prog env p2 ty)
    | PIf (Pred(p, args), pthen, pelse) ->
        PIf (Pred(p, List.map (go_arith env) args), go_prog env pthen ty, go_prog env pelse ty)
    | PIf _ -> failwith "PIf: " (* TODO: predicate を再帰的に見る *)
    | PEvent (ev, p) -> begin
      let states = transition_function ty ev in
      let terms =
        states |>
        List.map (fun state ->
          let env = max_env env (priority state) in
          go_prog env p state) in
      PEvent (ev, make_nondet terms)
    end
    (* TODO: 現状、Appの左が変数のときしか対応していない *)
    (* | PApp ((PVar var_name) as var, p2) -> begin
      match lookup_arg_type_by_body_type env var_name ty with
      | Some (argty, bodyty) -> begin
        let var = go_prog env var (ITFunc (argty, bodyty)) in
        assert (bodyty = ty);
        match argty with
        | IAInter tys -> begin
          let ps = List.map (fun (ty, m) -> go_prog (max_env env m) p2 ty) tys in
          make_app var ps
        end
        | IAInt -> assert false
      end
      | None -> failwith "unbounded var"
    end *)
    | PAppInt ((PVar var_name) as var, p2) -> begin
      match lookup_arg_type_by_body_type env var_name ty with
      | Some (argty, bodyty) -> begin
        let var = go_prog env var (ITFunc (argty, bodyty)) in
        assert (argty = IAInt);
        assert (bodyty = ty);
        let ps = go_arith env p2 in
        PAppInt (var, ps)
      end
      | None -> failwith "unbounded var (int)"
    end
    | PApp (p1, p2) -> begin
      let tys' = get_arg_type env p1 all_states in
      (* print_endline @@ "ty=" ^ show_itype ty;
      print_endline @@ "len=" ^ string_of_int (List.length tys');
      List.iter (fun ty -> print_endline @@ show_itype' ty) tys'; *)
      let tys' =
        List.filter
          (fun ty' -> match ty' with
            | ITFunc' (a, b) -> begin
              b = to_itype' ty
            end
            | _ -> false
          )
          tys' in
      match tys' with
      | [(ITFunc' (IAInter xs, ty')) as fty] -> begin
        let p1 = go_prog env p1 (from_itype' fty) in
        let ps = List.map (fun (ty, m) -> go_prog (max_env env m) p2 ty) xs in
        make_app p1 ps
      end
      | _ -> failwith @@ "PApp: " ^ show_program term ^ ", length=" ^ string_of_int (List.length tys')
    end
    (* | PApp (_, _) -> failwith "a" *)
    | PAppInt (_, _) -> failwith "b"
  and go_arith (env : itenv) (term : arith_expr) =
    (* type is integer *)
    (* 変数xの名前の変更をするだけ *)
    match term with
    | AVar x -> AVar x
    | AInt n -> AInt n
    | AOp (op, exprs) ->
      AOp (op, List.map (go_arith env) exprs) in
  go_prog env term


let to_itype_env (f, (t, i)) = (f, ITEInter (t, i, 0))

let decompose_ty' ty =
  let rec go ty acc = match ty with
    | ITState _ -> acc, ty
    | ITFunc (arg, body) -> go body (arg::acc)
  in
  go ty []

let trans_hes (env : itype_env) ((entry, program) : hes) transition_function priority initial_state all_states =
  let env' = List.map to_itype_env env in
  let program = List.map (fun (var, (ty, m)) ->
    let arg_tys, body_ty = decompose_ty' ty in
    match List.find_opt (fun {var=var'; _} -> var' = var) program with
    | Some {var; args; body} -> begin
      let arg_env =
        List.mapi (fun i ty ->
          let s = fst @@ List.nth args i in
          match ty with
          | IAInt -> [(s, ITEInt)]
          | IAInter xs ->
            List.map (fun (a, b) -> (s, ITEInter (a, b, 0))) xs
        ) arg_tys |>
        List.flatten in
      let prog = trans (env' @ arg_env) body transition_function priority all_states body_ty in
      let args =
        List.mapi (fun i ty ->
          let (s, ty') = List.nth args i in
          match ty with
          | IAInt -> [(s, ty')]
          | IAInter xs -> List.map (fun (a, b) -> (make_var_name s a b, ty')) xs
        ) arg_tys |>
        List.flatten in
      {var = make_var_name var ty m; args = args; body = prog}
    end
    | None -> failwith "trans_hes 1"
  ) env in
  let entry = trans env' entry transition_function priority all_states (ITState initial_state) in
  entry, program

let get_priority (env : itype_env) =
  env |>
  List.map (fun (s, (t, m)) -> (make_var_name s t m, m + 1))
