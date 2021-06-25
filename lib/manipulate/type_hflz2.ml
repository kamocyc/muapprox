open Hflmc2_syntax
module Env = Env_no_value

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type 'ty thflz =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty thflz * 'ty thflz
  | And    of 'ty thflz * 'ty thflz
  | Abs    of 'ty Id.t * 'ty thflz
  | Forall of 'ty Id.t * 'ty thflz
  | Exists of 'ty Id.t * 'ty thflz
  | App    of 'ty thflz * 'ty thflz
  | Arith  of 'ty tarith
  | Pred   of Formula.pred * 'ty tarith list
  [@@deriving eq,ord,show]

type enter_flag = Enter | NotEnter | EFVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type ptype = TInt | TBool | TFunc of ptype * ptype * enter_flag | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type 'a thes_rule = ('a Id.t * 'a Id.t list * 'a thflz * Fixpoint.t)
[@@deriving eq,ord,show]

type s_thes_rules = ptype thes_rule list
[@@deriving eq,ord,show]

type enter_flag_constraint = EF_Equal of enter_flag * enter_flag | EF_Le of enter_flag * enter_flag
[@@deriving eq,ord,show]

let show_enter_flag = function
  | Enter -> "T"
  | NotEnter -> "_"
  | EFVar id -> Hflmc2_syntax.Id.to_string id

let rec show_ptype = function
  | TInt -> "int"
  | TBool -> "bool"
  | TFunc (p1, p2, f) -> "(" ^ show_ptype p1 ^ "-" ^ (show_enter_flag f) ^ "->" ^ show_ptype p2 ^ ")"
  | TVar id -> Hflmc2_syntax.Id.to_string id

let get_free_variables phi =
  let rec go phi = match phi with
    | Bool _ -> []
    | Var v -> [v]
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Forall (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Exists (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | App (p1, p2) -> go p1 @ go p2
    | Arith a -> go_arith a
    | Pred (_, ps) -> List.map go_arith ps |> List.concat
  and go_arith a = match a with
    | Int _ -> []
    | Var v -> [v]
    | Op (_, ps) -> List.map go_arith ps |> List.concat
  in
  go phi

let rec subst_ptype ptype subst subst_flags =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (p1, p2, f) -> begin
    let f =
      match f with
      | EFVar id -> begin
        match List.find_opt (fun (k, _) -> Id.eq k id) subst_flags with
        | Some (_, v) -> v
        | None -> EFVar id
      end
      | f -> f in
    TFunc (subst_ptype p1 subst subst_flags, subst_ptype p2 subst subst_flags, f)
  end

let is_occur id ty =
  let rec go (ty : ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TBool -> false
    | TFunc (p1, p2, _) -> go p1 || go p2 in
  go ty

let compose_subst (id, ty) subst =
  let ty' = subst_ptype ty subst [] in
  (id, ty') :: subst
  
let unify (constraints : (ptype * ptype) list) =
  let rec is_equal_ptype t1 t2 =
    match t1, t2 with
    | TFunc (t11, t12, _), TFunc (t21, t22, _) ->
      (is_equal_ptype t11 t21) && (is_equal_ptype t12 t22)
    | TBool, TBool -> true
    | TInt, TInt -> true
    | TVar x1, TVar x2 -> Id.eq x1 x2
    | _ -> false
  in
  let subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair] [], subst_ptype p2 [pair] [])) xs in
  let flag_constraints = ref [] in
  let rec unify constraints = match constraints with
    | [] -> []
    | (t1, t2)::xs -> begin
      if is_equal_ptype t1 t2
      then unify xs
      else begin
        print_endline "unify2";
        print_endline @@ Hflmc2_util.show_pairs show_ptype show_ptype (constraints);
        match t1, t2 with
        | TFunc (t11, t12, f1), TFunc (t21, t22, f2) -> begin
          flag_constraints := (EF_Equal (f1, f2))::!flag_constraints;
          unify ((t11, t21) :: (t12, t22) :: xs)
        end
        | TVar t11, t2 -> begin
          if is_occur t11 t2 then failwith "occur1";
          compose_subst (t11, t2) (unify (subst xs (t11, t2)))
        end
        | t1, TVar t21 -> begin
          if is_occur t21 t1 then failwith "occur2";
          compose_subst (t21, t1) (unify (subst xs (t21, t1)))
        end
        | _ ->
          failwith @@ "unify (left: " ^ show_ptype t1 ^ " / right: " ^ show_ptype t2 ^ ")"
      end
    end in
  print_endline "constraints:";
  print_endline @@ (Hflmc2_util.show_pairs show_ptype show_ptype constraints);
  let r = unify constraints in
  (* print_endline "unify:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_ptype r); *)
  r, !flag_constraints

let to_thflzs hes =
  let rec go env (phi : 'a Hflz.t): ptype thflz = match phi with
    | Bool b -> Bool b
    | Var v ->
      let id = Env.lookup v env in
      Var id
    | Or (p1, p2) ->
      Or (go env p1, go env p2)
    | And (p1, p2) ->
      And (go env p1, go env p2)
    | Abs (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Abs (x, go (Env.update [x] env) p)
    | Forall (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Forall (x, go (Env.update [x] env) p)
    | Exists (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Exists (x, go (Env.update [x] env) p)
    | App (p1, p2) ->
      App (go env p1, go env p2)
    | Arith a ->
      Arith (go_arith env a)
    | Pred (e, ps) ->
      Pred (e, List.map (go_arith env) ps)
  and go_arith env phi = match phi with
    | Int i -> Int i
    | Var v ->
      let id = Env.lookup v env in
      Var id
    | Op (e, ps) ->
      Op (e, List.map (go_arith env) ps)
  in
  let rules =
    List.map
      (fun {Hflz.var; body; fix} ->
        let args, body = Hflz.decompose_abs body in
        let args = List.map (fun arg -> { arg with Id.ty = TVar (Id.gen ())}) args in
        let rec go base ls = match ls with
          | [] -> base
          | x::xs -> TFunc (x.Id.ty, go base xs, Enter)
        in 
        ( {var with ty = go TBool args}, args, body, fix )
      )
      hes in
  let global_env = List.map (fun (v, _, _, _) -> v) rules |> Env.create in
  List.map
    (fun (var, args, body, fix) ->
      let body = go (Env.update args global_env) body in
      ( var, args, body, fix )
    )
    rules
    
let generate_constraints (rules : ptype thes_rule list) : (ptype * ptype) list * enter_flag_constraint list =
  let filter_env env fvs =
    List.fold_left
      (fun env' fv ->
        let v = Env.lookup fv env in
        Env.update [v] env'
      )
      (Env.create [])
      fvs
  in
  let rec gen (env : (ptype * enter_flag) Env.t) (raw : ptype thflz)
      : ptype * (ptype * ptype) list * enter_flag_constraint list = match raw with
    | Bool _ -> (TBool, [], [])
    | Var v ->
      let id = Env.lookup v env in
      let ty, _ = id.ty in
      (ty, [], [])
    | Or (p1, p2) ->
      let t1, c1, f1 = gen env p1 in
      let t2, c2, f2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2, f1 @ f2)
    | And (p1, p2) ->
      let t1, c1, f1 = gen env p1 in
      let t2, c2, f2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2, f1 @ f2)
    | Abs (arg, body) -> begin
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, c, f = gen env body in
      (TFunc (arg.Id.ty, t, EFVar flag), c, f)
    end
    | Forall (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, c, f = gen env body in
      (t, (* (arg.Id.ty, TInt) :: *) c, f)
    | Exists (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, c, f = gen env body in
      (t, (* (arg.Id.ty, TInt) :: *) c, f)
    | App (p1, p2) ->
      let flag_a1 = Id.gen () in
      let t1, c1, f1 = gen env p1 in
      let (t2, c2, f2), flag_constrs =
        let fvs = get_free_variables p2 in
        let env' = filter_env env fvs in
        let flag_constrs =
          Env.to_list env |> List.map (fun id -> snd id.Id.ty)
          |> List.map (fun f -> EF_Le (EFVar flag_a1, f)) in
        gen env' p2, flag_constrs in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar, EFVar flag_a1)) :: c1 @ c2, f1 @ f2 @ flag_constrs)
    | Arith a ->
      let ty, c = gen_arith env a in
      (TInt, (TInt, ty) :: c, [])
    | Pred (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs), [])
  and gen_arith (env : (ptype * enter_flag) Env.t) (raw : ptype tarith)
      : ptype * (ptype * ptype) list = match raw with
    | Var v ->
      let id = Env.lookup v env in
      let ty, _ = id.ty in
      (ty, [(ty, TInt)])
    | Int _ -> (TInt, [])
    | Op (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    in
  let global_env =
    Env.create @@ (List.map (fun (v, _, _, _) -> v) rules
    |> List.map (fun id -> { id with Id.ty = (id.Id.ty, EFVar (Id.gen ())) } )) in
  List.map
    (fun ( _var, args, body, _fix ) ->
      let args = List.map (fun arg -> {arg with Id.ty=(arg.Id.ty, Enter)}) args in
      let _, constraints, flag_constraints = gen (Env.update args global_env) body in
      (constraints, flag_constraints)
    )
    rules
  |> List.split
  |> (fun (a, b) -> List.flatten a, List.flatten b)

let subst_program (rules : ptype thes_rule list) (subst : (unit Id.t * ptype) list) (subst_flags : (unit Id.t * enter_flag) list) =
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var { v with ty = subst_ptype v.ty subst subst_flags }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p) -> Abs ({ v with Id.ty = subst_ptype v.Id.ty subst subst_flags }, go p)
    | Forall (v, p) -> Forall ({ v with Id.ty = subst_ptype v.Id.ty subst subst_flags }, go p)
    | Exists (v, p) -> Exists ({ v with Id.ty = subst_ptype v.Id.ty subst subst_flags }, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Int i
    | Var v -> Var { v with ty = subst_ptype v.ty subst subst_flags }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun (var, args, body, fix) ->
    let var = { var with Id.ty = subst_ptype var.Id.ty subst subst_flags } in
    let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst subst_flags }) args in
    let body = go body in
    ( var, args, body, fix )
  ) rules

let rec to_ty = function
  | TFunc (arg, body, _) -> Type.TyArrow ({name = ""; id = 0; ty = to_argty arg}, to_ty body)
  | TBool -> Type.TyBool ()
  | TInt -> assert false
  | TVar _ -> assert false
and to_argty = function
  | TInt -> Type.TyInt
  | t -> Type.TySigma (to_ty t)
  
let to_hflz (rules : ptype thes_rule list) =
  let is_equal_ctype = (=) in
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Hflz.Bool b
    | Var v -> Var { v with ty = to_ty v.ty }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p) -> Abs ({ v with ty = to_argty v.ty }, go p)
    | Forall (v, p) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_equal_ctype v.Id.ty TInt);
        Forall ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | Exists (v, p) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_equal_ctype v.Id.ty TInt);
        Exists ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Arith.Int i
    | Var v ->
      assert (is_equal_ctype v.ty TInt);
      Var { v with ty = `Int }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun (var, args, body, fix) ->
    let var = { var with Id.ty = to_ty var.Id.ty } in
    let args = List.map (fun v -> { v with Id.ty = to_argty v.Id.ty }) args in
    let body = go body in
    let rec go ls body = match ls with
      | [] -> body
      | x::xs -> Hflz.Abs (x, go xs body) in
    let body = go args body in
    { Hflz.var; body; fix }
  ) rules

let unify_flags constraints =
  let equals, les =
    Hflmc2_util.partition_map
      ~f:(fun c ->
        match c with
        | EF_Equal (x1, x2) -> `Fst (x1, x2)
        | EF_Le (x1, x2) -> `Snd (x1, x2))
      constraints
    in
  let subst_flag id f pairs =
    List.map
      (fun (b1, b2) ->
        (match b1 with
        | EFVar v when Id.eq v id -> f
        | _ -> b1),
        (match b2 with
        | EFVar v when Id.eq v id -> f
        | _ -> b2)
      )
      pairs
    in
  let rec go equals les subst_acc =
    match equals with
    | (a1, a2)::equals -> begin
      let pair_opt =
        match a1, a2 with
        | EFVar id1, _ -> Some (id1, a2)
        | _, EFVar id2 -> Some (id2, a1)
        | Enter, Enter -> None
        | NotEnter, NotEnter -> None
        | _ -> failwith "unify failed"
      in
      let equals, les, subst_acc =
        match pair_opt with
        | Some (id, a) ->
          subst_flag id a equals,
          subst_flag id a les,
          (id, a)::subst_acc
        | None ->
          equals, les, subst_acc
      in
      go equals les subst_acc
    end
    | [] -> [], subst_acc
  in
  let rec go_les les acc_subst =
    let determined, les =
      Hflmc2_util.partition_map
        ~f:(fun le ->
          match le with
          | (Enter, EFVar f2) -> `Fst (f2, Enter)
          | (EFVar f1, NotEnter) -> `Fst (f1, NotEnter)
          | _ -> `Snd le
        )
        les in
    match determined with
    | [] -> les, acc_subst
    | _ ->
      let les =
        List.fold_left
          (fun les (id, f) ->
            subst_flag id f les
          )
          les
          determined
      in
      go_les les (acc_subst @ determined)
  in
  let les, subst_acc = go equals les [] in
  let les, subst_acc' = go_les les [] in
  let les =
    List.filter
      (fun le ->
        match le with
        | (Enter, Enter)
        | (NotEnter, NotEnter)
        | (NotEnter, Enter) -> false
        | (Enter, NotEnter) -> failwith "a"
        | _ -> true
      )
      les in
  let subst_acc'' =
    List.map
      (fun le ->
        match le with
        | (EFVar id1, EFVar id2) ->
          [(id1, NotEnter); (id2, NotEnter)]
        | (EFVar id1, Enter) ->
          [(id1, NotEnter)]
        | (NotEnter, EFVar id2) ->
          [(id2, NotEnter)]
        | _ -> assert false
      )
      les
    |> List.concat in
  subst_acc @ subst_acc' @ subst_acc''  
  
let infer_thflz_type (rules : ptype thes_rule list): ptype thes_rule list =
  let constraints, flag_constraints = generate_constraints rules in
  print_endline "infer1";
  let substitution, flag_constraints' = unify constraints in
  print_endline "infer2";
  let flag_substitution = unify_flags (flag_constraints @ flag_constraints') in
  print_endline "infer3";
  let rules = subst_program rules substitution flag_substitution in
  rules

(* TODO: debug *)
let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let rules = to_thflzs rules in
  print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules;
  let rules = infer_thflz_type rules in
  print_endline "infer_thflz_type (2)";
  print_endline @@ show_s_thes_rules rules;
  let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  print_endline @@ Hflz.show_hes Type.pp_simple_ty hes; 
  hes
