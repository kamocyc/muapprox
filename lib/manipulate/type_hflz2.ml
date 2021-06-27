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
  
module Print_temp = struct
  open Hflmc2_syntax.Print
    
  let pid : Stdlib__format.formatter -> int -> unit = fun fmt _i ->
    (* Fmt.pf fmt "<%d>" i *)
    Fmt.string fmt ""
  
  let p_id ppf id = Fmt.pf ppf "@[<h>%a@]" pid id.Id.id

  let rec gen_arith_ : 'avar t_with_prec -> ptype tarith t_with_prec =
    fun avar_ prec ppf a ->
      let show_op = function | (Arith.Op (op',[a1;a2])) -> begin
        let op_prec = Prec.of_op op' in
        let prec_l = Prec.(succ_if (not @@ op_is_leftassoc op') op_prec) in
        let prec_r = Prec.(succ_if (not @@ op_is_rightassoc op') op_prec) in
        show_paren (prec > op_prec) ppf "@[<1>%a@ %a@ %a@]"
          (gen_arith_ avar_ prec_l) a1
          op op'
          (gen_arith_ avar_ prec_r) a2
      end | _ -> assert false
      in
      match a with
      | Int (n) ->
        if n >= 0 then
          Fmt.int ppf n
        else
          (Fmt.string ppf "("; Fmt.int ppf n; Fmt.string ppf ")";)
      | Var (x) -> avar_ prec ppf x
      | Op (_, _) -> show_op a
      (* | _ -> assert false *)
      
  (* let gen_arith : 'avar t_with_prec -> ptype tarith t =
    fun avar_ ppf a -> gen_arith_ avar_ Prec.zero ppf a *)
  let ignore_prec orig _prec ppf x =
        orig ppf x
  let id_ : 'ty Id.t t_with_prec =
    ignore_prec id
  let arith_ : Prec.t -> ptype tarith Fmt.t =
    fun prec ppf a -> gen_arith_ id_ prec ppf a
  
  let pred : Formula.pred t =
    fun ppf pred -> match pred with
      | Eq  -> Fmt.string ppf "="
      | Neq -> Fmt.string ppf "!="
      | Le  -> Fmt.string ppf "<="
      | Ge  -> Fmt.string ppf ">="
      | Lt  -> Fmt.string ppf "<"
      | Gt  -> Fmt.string ppf ">"
  let pred_ : Formula.pred t_with_prec =
    ignore_prec pred
  
  let rec hflz_ : (Prec.t -> ptype Fmt.t) -> Prec.t -> ptype thflz Fmt.t =
    fun format_ty_ prec ppf (phi : ptype thflz) -> match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x -> Fmt.pf ppf "%a" id x
      | Or (phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ \\/ %a@]"
            (hflz_ format_ty_ Prec.or_) phi1
            (hflz_ format_ty_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ /\\ %a@]"
            (hflz_ format_ty_ Prec.and_) phi1
            (hflz_ format_ty_ Prec.and_) phi2
      | Abs (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
            id x
            (format_ty_ Prec.(succ arrow)) x.ty
            (hflz_ format_ty_ Prec.abs) psi
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | Exists (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (true) ppf "@[<1>%a@ %a@]"
            (hflz_ format_ty_ Prec.app) psi1
            (hflz_ format_ty_ Prec.(succ app)) psi2
      | Arith (a) ->
        arith_ prec ppf a
      | Pred (pred', [f1; f2]) ->
          (* p_id ppf sid;  *)
          Fmt.pf ppf "@[<1>%a@ %a@ %a@]"
            (arith_ prec) f1
            pred pred'
            (arith_ prec) f2
      | Pred _ -> assert false

  let hflz : (Prec.t -> 'ty Fmt.t) -> 'ty thflz Fmt.t =
    fun format_ty_ -> hflz_ format_ty_ Prec.zero

(* 'a Id.t * 'a Id.t list * 'a thflz * Fixpoint.t *)
  let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf (var, args, body, fix) ->
      Fmt.pf ppf "@[<2>%s %a =%a@ %a@]"
        (Id.to_string var)
        (pp_print_list ~pp_sep:Print_syntax.PrintUtil.fprint_space (fun ppf arg -> fprintf ppf "(%s : %a)" (Id.to_string arg) (format_ty_ Prec.zero) arg.Id.ty))
        args
        fixpoint fix
        (hflz format_ty_) body

  let hflz_hes : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
  
  (* let print_hes rules = (Print.printf "%a\n" (hflz_hes (fun _p fmt ty -> pp_ptype fmt ty)) rules); Print.print_flush (); *)

end

let show_enter_flag = function
  | Enter -> "T"
  | NotEnter -> "_"
  | EFVar id -> Hflmc2_syntax.Id.to_string id

let rec show_ptype = function
  | TInt -> "int"
  | TBool -> "bool"
  | TFunc (p1, p2, f) -> "(" ^ show_ptype p1 ^ "-" ^ (show_enter_flag f) ^ "->" ^ show_ptype p2 ^ ")"
  | TVar id -> Hflmc2_syntax.Id.to_string id

let show_enter_flag_constraint = function
  | EF_Equal (f1, f2) -> show_enter_flag f1 ^ "=" ^ show_enter_flag f2
  | EF_Le (f1, f2) -> show_enter_flag f1 ^ "<=" ^ show_enter_flag f2
  
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

let rec subst_ptype ?(not_found_to_enter=false) ptype subst subst_flags =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> subst_ptype ~not_found_to_enter v [] subst_flags
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (p1, p2, f) -> begin
    let f =
      match f with
      | EFVar id -> begin
        match List.find_opt (fun (k, _) -> Id.eq k id) subst_flags with
        | Some (_, v) -> v
        | None -> begin
          if not_found_to_enter then Enter else EFVar id
        end
      end
      | f -> f in
    TFunc (
      subst_ptype ~not_found_to_enter p1 subst subst_flags,
      subst_ptype ~not_found_to_enter p2 subst subst_flags, f)
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
        (* print_endline "unify2";
        print_endline @@ Hflmc2_util.show_pairs show_ptype show_ptype (constraints); *)
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
  (* print_endline "constraints:";
  print_endline @@ (Hflmc2_util.show_pairs show_ptype show_ptype constraints); *)
  let r = unify constraints in
  print_endline "unify:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_ptype r);
  print_endline "flag_constraints (to solve):";
  print_endline @@ (Hflmc2_util.show_list show_enter_flag_constraint !flag_constraints);
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
  let subst_ptype ty subst subst_flags =
    print_endline "subst_ptype 1";
    print_endline @@ show_ptype ty;
    print_endline @@ Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_flags;
    subst_ptype ~not_found_to_enter:true ty subst subst_flags in
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

let to_hflz_with_same_type (rules : ptype thes_rule list) =
  let is_int_type ty = ty = TInt in
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Hflz.Bool b
    | Var v -> Var v
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p) -> Abs ({v with ty = Type.TySigma v.ty}, go p)
    | Forall (v, p) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_int_type v.Id.ty);
        Forall ({ v with Id.ty = Type.TySigma TInt }, go p)
      end
    end
    | Exists (v, p) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_int_type v.Id.ty);
        Exists ({ v with Id.ty = Type.TySigma TInt }, go p)
      end
    end
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Arith.Int i
    | Var v ->
      assert (is_int_type v.ty);
      Var { v with ty = `Int }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun (var, args, body, fix) ->
    let var = var in
    let args = List.map (fun v -> v) args in
    let body = go body in
    let rec go ls body = match ls with
      | [] -> body
      | x::xs -> Hflz.Abs ({x with ty=Type.TySigma x.Id.ty}, go xs body) in
    let body = go args body in
    { Hflz.var; body; fix }
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
  let is_int_type ty = ty = TInt in
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
        assert (is_int_type v.Id.ty);
        Forall ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | Exists (v, p) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_int_type v.Id.ty);
        Exists ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Arith.Int i
    | Var v ->
      assert (is_int_type v.ty);
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
  (* pairs[f/id] *)
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
  let compose_flags_subst (id, flag) subst =
    let flag =
      match flag with
      | EFVar fv -> begin
        match List.find_opt (fun (id, _) -> Id.eq id fv) subst with
        | Some (_, v) -> v
        | None -> EFVar fv
      end
      | _ -> flag in
    (id, flag) :: subst
  in
  (* subst1 \circ subst2 *)
  let compose_flags_substs subst1 subst2 =
    (List.map
      (fun (id, v) ->
        let v =
          match v with
          | EFVar x -> begin
            match List.find_opt (fun (id', _) -> Id.eq id' x) subst1 with
            | Some (_, v') -> v'
            | None -> EFVar x
          end
          | _ -> v
        in
        (id, v)
      )
      subst2) @ subst1
  in
  let rec go equals les =
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
      match pair_opt with
      | Some (id, a) ->
        let equals = subst_flag id a equals in
        let les = subst_flag id a les in
        let subst, les = go equals les in
        compose_flags_subst (id, a) subst, les
      | None ->
        go equals les
    end
    | [] -> [], les
  in
  let rec go_les_sub determined les =
    match determined with
    | (EFVar id, f)::determined ->
      let les = subst_flag id f les in
      let determined = subst_flag id f determined in
      let subst, les = go_les_sub determined les in
      compose_flags_subst (id, f) subst, les
    | (_, _)::_ -> assert false
    | [] -> [], les
  in
  let rec go_les les =
    let determined, les =
      Hflmc2_util.partition_map
        ~f:(fun le ->
          match le with
          | (Enter, EFVar f2) -> `Fst (EFVar f2, Enter)
          | (EFVar f1, NotEnter) -> `Fst (EFVar f1, NotEnter)
          | _ -> `Snd le
        )
        les in
    match determined with
    | [] -> [], les
    | _ ->
      let subst_acc, les = go_les_sub determined les in
      let subst_acc', les = go_les les in
      compose_flags_substs subst_acc subst_acc', les
  in
  let subst_acc, les = go equals les in
  let subst_acc', les = go_les les in
  (* TODO: substitutionのcomposeを順番にやる *)
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
    |> List.concat
    |> Hflmc2_util.remove_duplicates (=) in
  let composed = compose_flags_substs (compose_flags_substs subst_acc' subst_acc'') subst_acc in
  print_endline "flag_constraints (subst_acc):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc);
  print_endline "flag_constraints (subst_acc'):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc');
  print_endline "flag_constraints (subst_acc''):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc'');
  print_endline "flag_constraints (composed):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed);
  (* print_endline "flag_constraints (solved):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed); *)
  composed
  
let infer_thflz_type (rules : ptype thes_rule list): ptype thes_rule list =
  let constraints, flag_constraints = generate_constraints rules in
  let substitution, flag_constraints' = unify constraints in
  let flag_substitution = unify_flags (flag_constraints @ flag_constraints') in
  let rules = subst_program rules substitution flag_substitution in
  rules

let rec pp_ptype prec ppf ty =
  match ty with
  | TBool ->
    Fmt.pf ppf "bool"
  | TInt ->
    Fmt.pf ppf "int"
  | TFunc (ty1, ty2, f) ->
    Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a -%s->@ %a@]"
      (pp_ptype Print.Prec.(succ arrow)) ty1
      (show_enter_flag f)
      (pp_ptype Print.Prec.arrow) ty2
  | TVar (id) ->
    Fmt.pf ppf "%s" (Id.to_string id)
  
(* TODO: debug *)
let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let rules = to_thflzs rules in
  (* print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = infer_thflz_type rules in
  let () =
    (* let rules = to_hflz_with_same_type rules in
    let rules = Hflz.decompose_entry_rule rules in *)
    print_endline "to_hflz_with_same_type:";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    in
  print_endline "infer_thflz_type (2)";
  print_endline @@ show_s_thes_rules rules;
  let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  print_endline @@ Hflz.show_hes Type.pp_simple_ty hes; 
  hes
