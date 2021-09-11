open Hflmc2_syntax
open Itype
open Raw_program
open Program

module Program2 = Program

let show_id_st id = Id.show Type.pp_simple_ty id

(* let nondet_demonic_event = "demonic_non_determinism"
let nondet_angelic_event = "angelic_non_determinism" *)
let nondet_dummy_event = ""

let upto m =
  let rec go m = if m = 0 then [0] else m :: (go (m - 1)) in    
  go m

(* simple typeに対するcanonical intersection typeを返す *)
let canonical_it (simple_type : Type.simple_ty) states max_m =
  let product xs ys =
    List.map (fun x -> List.map (fun y -> (x, y)) ys) xs |> List.flatten in
  let ms = upto max_m in
  let rec go simple_type = match simple_type with
    | Type.TyBool () -> states |> List.map (fun s -> ITState s)
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
let canonical_it_program (prog : program) (states : state list) (max_m : int) =
  let ms = upto max_m in
  let program, funcs = prog in
  let prog_ty = List.map (fun {var; _} ->
    canonical_it (var.ty) states max_m |>
      List.map (fun s ->
        List.map (fun mm -> 
          (Id.remove_ty var, (s, mm))
        ) ms
      ) |> List.flatten
  ) funcs |> List.flatten in
  prog_ty
  
let max_env (env : itenv) (m : int): itenv =
  env |>
  List.map (function
    | v, ITEInt -> v, ITEInt
    | v, ITEInter (t, m1, m2) -> v, ITEInter (t, m1, max m2 m))

let lookup_with_itype_base env x ty f n =
  match List.filter_map f env with
  | [] -> failwith @@ "lookup_with_itype_base: not found (var=" ^ show_id_st x ^ ", ty=" ^ show_itype ty ^ ", from=" ^ n ^ ")"
  | xs -> begin
    let m' = List.fold_left (fun max (_, _, m') -> if max < m' then m' else max) (-1) xs in
    match List.filter (fun (_, m, m') -> m = m') xs with
    | [] -> failwith @@ "lookup_with_itype_base: max priority mismatch (var=" ^ show_id_st x ^ ", ty=" ^ show_itype ty ^ ", max=" ^ string_of_int m' ^ ", priorities=" ^ (List.map (fun (_, m, _) -> string_of_int m) xs |> String.concat ", ") ^ ", from=" ^ n ^ ")"
    | [(ty, m, _)] -> Some (ty, m)
    | _ -> failwith "lookup_with_itype_base: false"
  end
 
let lookup_with_itype env x ty =
  lookup_with_itype_base env x ty (fun (id, ty') ->
    if Id.eq id x then begin
      match ty' with
      | ITEInter (t, m, m') -> if eq_itype t ty then Some (t, m, m') else None
      | ITEInt -> None
    end else None
  ) "var"

let lookup_arg_type_by_body_type env x ty =
  lookup_with_itype_base env x ty (fun (id, ty') ->
    if Id.eq id x then begin
      match ty' with
      | ITEInter ((ITFunc (_, body)) as t, m, m') -> if eq_itype body ty then Some (t, m, m') else None
      | _ -> None
    end else None
  ) "fun_body"
  |> Option.map (fun (t, m) -> match t with ITFunc (arg, body) -> (arg, body) | _ -> assert false)

let make_var_name (x : string) (v : itype) (m : int) =
  x ^ "_{" ^ show_itype v ^ "," ^ string_of_int m ^"}"

let make_nondet terms = 
  let rec go : Program2.program_expr list -> Program2.program_expr = function 
    | [] -> failwith "make_nondet"
    | [x1] -> x1
    | [x1; x2] -> PNonDet (x1, x2, None, Some nondet_dummy_event)
    | x::xs -> PNonDet(x, go xs, None, Some nondet_dummy_event) in
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
      match List.find_all (fun (id, _) -> Id.eq id var) env |> List.map (fun (_, v) -> v) with
      | [] -> failwith "unbounded"
      | ty -> begin
        let results = List.map to_itype'_from_envtype ty in
        (* print_endline @@ Id.to_string var;
        print_endline @@ show_itenv env;
        print_endline @@ string_of_int @@ List.length results; *)
        results
      end
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
              print_endline @@ show_program_expr term;
              print_endline @@ string_of_int @@ List.length tys;
              print_endline @@ string_of_int @@ List.length tys2;
              assert (List.length tys = List.length tys2);
              let b =
                List.mapi (fun i (ty1, _) ->
                  let b = eq_itype' (to_itype' ty1) (List.nth tys2 i) in
                  if not b then print_endline @@ "differ i=" ^ string_of_int i ^ ", ty1=" ^ show_itype' (to_itype' ty1) ^ " / ty2=" ^ show_itype' (List.nth tys2 i);
                  b
                ) tys |>
                List.for_all (fun x -> x) in
              print_endline @@ "term=" ^ show_program_expr term;
              b
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
      assert (List.for_all2 eq_itype' ty1 ty2);
      ty1
    end
    | PNonDet (p1, p2, _, _) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      assert (List.for_all2 eq_itype' ty1 ty2);
      ty1
    end
    | PEvent (e, p1) -> go env p1
    in
  go env term
  
let make_app v xs =
  let rec go (xs: Program2.program_expr list): Program2.program_expr = match xs with
    | [] -> v
    | x::xs -> PApp (go xs, x) in
  go (List.rev xs)

let trans
    (env : itenv)
    (term : program_expr)
    (transition_function : state * symbol -> state list)
    priority
    all_states =
  let transition_function ty ev = match ty with
    | ITFunc  _ -> failwith "transition_function"
    | ITState s -> transition_function (s, ev) |> List.map (fun s -> ITState s)
  in
  let priority ty = match ty with
    | ITFunc _ -> failwith "priority"
    | ITState s -> priority s
  in
  let rec go_prog (env : itenv) (term : program_expr) (ty : itype): Program2.program_expr = (* print_endline @@ "go_prog:" ^ show_program term; *) match term with
    | PUnit -> PUnit
    | PVar x -> begin
      match lookup_with_itype env x ty with
      | None -> failwith @@ "PVar: not found (" ^ Id.show Type.pp_simple_ty x ^ ": (" ^ show_itype ty ^ ", " ^ string_of_int 0 ^ ")"
      | Some (v, m) -> PVar ({x with name = make_var_name x.Id.name v m})
    end
    | PNonDet (p1, p2, n, _) -> PNonDet (go_prog env p1 ty, go_prog env p2 ty, n, Some nondet_dummy_event)
    | PIf (pred, pthen, pelse) -> PIf (go_pred env pred, go_prog env pthen ty, go_prog env pelse ty)
    | PEvent (ev, p) -> begin
      let states = transition_function ty (Symbol ev) in
      let terms =
        states |>
        List.map (fun state ->
          let env = max_env env (priority state) in
          go_prog env p state) in
      PEvent (ev, make_nondet terms)
    end
    | PAppInt (p1, p2) -> begin
      let tys' = get_arg_type env p1 all_states |> List.sort_uniq compare in
      let tys' =
        List.filter
          (fun ty' -> match ty' with
            | ITFunc' (IAInt, b) -> eq_itype' b (to_itype' ty)
            | _ -> false
          )
          tys' in
      match tys' with
      | [(ITFunc' (IAInt, ty')) as fty] -> begin
        let p1 = go_prog env p1 (from_itype' fty) in
        let ps = go_arith env p2 in
        PAppInt (p1, ps)
      end
      | _ -> failwith @@ "PAppInt: " ^ show_program_expr term ^ ", length=" ^ string_of_int (List.length tys')
    end
    | PApp (p1, p2) -> begin
      (* p1の型を取得（一般には一意にならない） *)
      let tys' = get_arg_type env p1 all_states |> List.sort_uniq compare in
      (* print_endline @@ "ty=" ^ show_itype ty;
      print_endline @@ "len=" ^ string_of_int (List.length tys');
      List.iter (fun ty -> print_endline @@ show_itype' ty) tys'; *)
      (* 戻り値の型に一致するものだけを抽出 *)
      (* TODO: ここで、必ずしも一意にならない？ *)
      let tys' =
        List.filter
          (fun ty' -> match ty' with
            | ITFunc' (a, b) -> eq_itype' b (to_itype' ty)
            | _ -> false
          )
          tys' in
      match tys' with
      | [(ITFunc' (IAInter xs, ty')) as fty] -> begin
        let p1 = go_prog env p1 (from_itype' fty) in
        let ps = List.map (fun (ty, m) -> go_prog (max_env env m) p2 ty) xs in
        make_app p1 ps
      end
      | _ -> failwith @@ "PApp: " ^ show_program_expr term ^ ", length=" ^ string_of_int (List.length tys')
    end
  and go_pred (env : itenv) (pred : program_predicate) = 
    match pred with
    | Pred (p, args) -> Pred(p, List.map (go_arith env) args)
    | And (p1, p2) -> And (go_pred env p1, go_pred env p2)
    | Or (p1, p2) -> Or (go_pred env p1, go_pred env p2)
    | Bool b -> Bool b
  and go_arith (env : itenv) (term : arith_expr) =
    (* type is integer *)
    (* 変数xの名前の変更をするだけ. ただし、整数型の変数は名前を変える必要はない（数を増やさないため） *)
    match term with
    | AVar x -> AVar x
    | AInt n -> AInt n
    | ANonDet (n, e) -> ANonDet (n, e)
    | AOp (op, exprs) ->
      AOp (op, List.map (go_arith env) exprs) in
  go_prog env term


let to_itype_env (f, (t, i)) = (f, ITEInter (t, i, 0))

let decompose_ty' ty =
  let rec go ty acc = match ty with
    | ITState _ -> acc |> List.rev, ty
    | ITFunc (arg, body) -> go body (arg::acc)
  in
  go ty []

let to_funty args =
  let rec go args = match args with
    | [] -> Type.TyBool ()
    | x::xs -> Type.TyArrow ({ty=x; name=""; id=0}, go xs) in
  go args

let substitute env phi =
  let rec hflz (phi : program_expr) = match phi with
    | PVar x ->
      begin match IdMap.lookup env x with
        | t -> t
        | exception Core.Not_found_s _ -> PVar x
      end
    | PUnit -> phi
    | PIf (p1, p2, p3) ->
      PIf (pred p1, hflz p2, hflz p3)
    | PEvent (e, p) -> PEvent (e, hflz p)
    | PNonDet (p1, p2, n, e) -> PNonDet (hflz p1, hflz p2, n, e)
    | PApp (p1, p2) -> PApp (hflz p1, hflz p2)
    | PAppInt (p1, p2) -> PAppInt (hflz p1, arith p2)
  and pred (phi : program_predicate) = match phi with
    | Pred (o, ps) -> Pred (o, List.map arith ps)
    | And (p1, p2) -> And (pred p1, pred p2)
    | Or (p1, p2) -> Or (pred p1, pred p2)
    | Bool _ -> phi
  and arith (phi : arith_expr) = match phi with
    | AVar v -> 
      AVar v
      (* begin match IdMap.lookup env v with
        | t -> t
        | exception Core.Not_found_s _ -> AVar v
      end *)
    | AInt _ -> phi
    | ANonDet (n, e) -> ANonDet (n, e)
    | AOp (op, ps) -> AOp (op, List.map arith ps) in
  hflz phi

let convert_itype_to_simple_type (itype : itype) =
  let open Type in
  let rec go_itype (itype : itype) = match itype with
    | ITState _ -> TyBool ()
    | ITFunc (IAInt, body) ->
      TyArrow ({name=""; id=0; ty = TyInt}, go_itype body)
    | ITFunc (IAInter xs, body) ->
      let rec go t b= match t with
        | x::xs -> TyArrow ({name=""; id=0; ty=TySigma x}, go xs b)
        | [] -> b
      in
      let tys = List.map (fun (t, _) -> go_itype t) xs in
      go tys (go_itype body) in
  go_itype itype
    
let trans_program
    (env : itype_env)
    ((entry, program) : program)
    (transition_function : state * symbol -> state list)
    (priority : state -> int)
    (initial_state : state)
    (all_states : state list) : program =
  let env' = List.map to_itype_env env in
  let program = List.map (fun (var, (ty, m)) ->
    print_endline @@ show_itype ty;
    let arg_tys, body_ty = decompose_ty' ty in
    print_endline @@ (List.map show_iarg arg_tys |> String.concat ";");
    match List.find_opt (fun {var=var'; _} -> Id.eq var' var) program with
    | Some {var; args; body} -> begin
      assert (List.length args = List.length arg_tys);
      let arg_env =
        List.mapi (fun i ty ->
          let s = Id.remove_ty (List.nth args i) in
          match ty with
          | IAInt -> [(s, ITEInt)]
          | IAInter xs ->
            List.map (fun (a, b) -> (s, ITEInter (a, b, 0))) xs
        ) arg_tys |>
        List.flatten in
      let prog = trans (env' @ arg_env) body transition_function priority all_states body_ty in
      let args =
        List.mapi (fun i ty ->
          let ({Id.name = s; ty = ty'} as argid) = List.nth args i in
          match ty with
          | IAInt -> [argid]
          | IAInter xs ->
            List.map (fun (tyin, m) ->
              { argid with
                name = make_var_name s tyin m;
                ty = Type.TySigma (convert_itype_to_simple_type tyin)
              }
            ) xs
        ) arg_tys |>
        List.flatten in
      let prog =
        List.fold_left (fun prog arg ->
          match arg.Id.ty with
          | Type.TyInt -> prog
          | Type.TySigma (ty) -> begin
            let arg_env = IdMap.of_list [Id.remove_ty arg, PVar { arg with ty = ty }] in
            substitute arg_env prog
          end
        )
        prog
        args in
      {
        var = {
          var with
            name = make_var_name var.Id.name ty m;
            ty = to_funty (List.map (fun i -> i.Id.ty) args)
        };
        args = args;
        body = prog
      }
    end
    | None -> failwith @@ "trans_program 1 (not found: " ^ Id.to_string var ^ ")"
  ) env in
  (* 型を合わせる *)
  let prog_env = IdMap.of_list @@ List.map (fun rule -> (Id.remove_ty rule.var, PVar rule.var)) program in
  let program =
    List.map (fun rule ->
      { rule with body = substitute prog_env rule.body }
    )
    program in
  let entry = trans env' entry transition_function priority all_states (ITState initial_state) in
  let entry = substitute prog_env entry in
  entry, program

let get_priority (env : itype_env) =
  env |>
  List.map (fun (v, (t, m)) -> ({ v with Id.name = make_var_name v.Id.name t m}, m + 1))
