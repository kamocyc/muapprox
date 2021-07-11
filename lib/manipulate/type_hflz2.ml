open Hflmc2_syntax
module Env = Env_no_value

let simplified_type = ref false

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type 'ty thflz =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty thflz * 'ty thflz
  | And    of 'ty thflz * 'ty thflz
  | Abs    of 'ty Id.t * 'ty thflz * 'ty
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

type 'a fixpoint_type = {var: 'a Id.t; args: 'a Id.t list}
[@@deriving eq,ord,show]

type 'a thes_rule = {outer: 'a fixpoint_type; inner: 'a fixpoint_type; body: 'a thflz; fix: Fixpoint.t}
[@@deriving eq,ord,show]

type s_thes_rules = ptype thes_rule list
[@@deriving eq,ord,show]

type enter_flag_constraint = EF_Equal of enter_flag * enter_flag | EF_Le of enter_flag * enter_flag
[@@deriving eq,ord,show]

type recursive_flag = Recursive | NotRecursive
[@@deriving eq,ord,show]

let get_thflz_type phi =
  let rec go phi = match phi with
    | Bool _ -> TBool
    | Var v -> v.ty
    | Or _ -> TBool
    | And _ -> TBool
    | Abs (_, _, lty) -> lty
    | Forall (_, body) -> go body
    | Exists (_, body) -> go body
    | App (p1, _) -> begin
      let ty1 = go p1 in
      match ty1 with
      | TFunc (_, t2, _) -> t2
      | _ -> assert false
    end
    | Pred (_, _) -> TBool
    | Arith _ -> TInt
  in
  go phi

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

module Print_temp = struct
  open Hflmc2_syntax.Print

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
      
  let ignore_prec orig _prec ppf x =
        orig ppf x
  let id_ : 'ty Id.t t_with_prec =
    ignore_prec id
  let arith_ : Prec.t -> ptype tarith Fmt.t =
    fun prec ppf a -> gen_arith_ id_ prec ppf a
  
  let rec hflz_ : (Prec.t -> ptype Fmt.t) -> Prec.t -> ptype thflz Fmt.t =
    fun format_ty_ prec ppf (phi : ptype thflz) -> match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x ->
        (* Fmt.pf ppf "(%a : %a)" id x (format_ty_ Prec.zero) x.ty *)
        Fmt.pf ppf "%a" id x
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
      | Abs (x, psi, ty) -> begin
          let f_str = 
            match ty with
            | TFunc (_, _, f) -> show_enter_flag f
            | _ -> "" in
          show_paren (prec > Prec.abs) ppf "@[<1>λ%a:{%s}%a.@,%a@]"
            id x
            f_str
            (format_ty_ Prec.(succ arrow)) x.ty
            (hflz_ format_ty_ Prec.abs) psi
      end
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | Exists (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | App (psi1, psi2) -> begin
          let f_str =
            match get_thflz_type psi1 with
            | TFunc (_, _, f) -> begin
              match f with
              | Enter -> "{T}"
              | NotEnter -> "{_}"
              | EFVar _ -> ""
            end
            | _ -> ""
          in
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %s%a@]"
            (hflz_ format_ty_ Prec.app) psi1
            f_str
            (hflz_ format_ty_ Prec.(succ app)) psi2
      end
      | Arith a ->
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

  let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf {outer; inner; body; fix} ->
      let rec to_flags ty =
        match ty with
        | TFunc (_, ty, f) -> f :: to_flags ty
        | _ -> []
      in
      Fmt.pf ppf "@[<2>%s %a =%a@ %a@]"
        (Id.to_string outer.var)
        (pp_print_list ~pp_sep:Print_syntax.PrintUtil.fprint_space (fun ppf ((arg, _f1), f2) -> fprintf ppf "(%s : {%s}(%a))" (Id.to_string arg) (* show_enter_flag f1 *) (show_enter_flag f2) (format_ty_ Prec.zero) arg.Id.ty))
        (List.combine (List.combine outer.args (to_flags outer.var.Id.ty)) (to_flags inner.var.Id.ty))
        fixpoint fix
        (hflz format_ty_) body

  let hflz_hes : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
  
end

let rec pp_ptype prec ppf ty =
  if !simplified_type then begin
    match ty with
    | TBool ->
      Fmt.pf ppf "bool"
    | TInt ->
      Fmt.pf ppf "int"
    | TFunc (ty1, ty2, _) ->
      Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a ->@ %a@]"
        (pp_ptype Print.Prec.(succ arrow)) ty1
        (pp_ptype Print.Prec.arrow) ty2
    | TVar (id) ->
      Fmt.pf ppf "%s" (Id.to_string id)
  end else begin
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
    
  end
let get_free_variables phi =
  let rec go phi = match phi with
    | Bool _ -> []
    | Var v -> [v]
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
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

let get_thflz_type env phi =
  let rec go env phi = match phi with
    | Bool _ -> TBool
    | Var v -> begin
      match List.find_all (fun v' -> Id.eq v v') env with
      | [id'] -> begin
        assert (id'.ty = v.ty);
        v.ty
      end
      | _ -> assert false
    end
    | Or (p1, p2) ->
      assert (go env p1 = TBool);
      assert (go env p2 = TBool);
      TBool
    | And (p1, p2) ->
      assert (go env p1 = TBool);
      assert (go env p2 = TBool);
      TBool
    | Abs (x, p, lty) -> begin
      let ty = go (x::env) p in
      let f =
        match lty with
        | TFunc (p1, p2, f') ->
          assert (ty = p2);
          assert (x.Id.ty = p1);
          f'
        | _ -> assert false
      in
      TFunc (x.Id.ty, ty, f)
    end
    | Forall (x, body) ->
      go (x::env) body
    | Exists (x, body) ->
      go (x::env) body
    | App (p1, p2) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      match ty1 with
      | TFunc (t1, t2, _) -> begin
        assert (t1 = ty2);
        t2
      end
      | _ -> assert false
    end
    | Pred (_, args) ->
      List.iter (fun arg ->
        let ty = go_arith env arg in
        assert (ty = TInt);
      ) args;
      TBool
    | Arith a ->
      assert (go_arith env a = TInt);
      TInt
  and go_arith env a = match a with
    | Int _ -> TInt
    | Var v -> begin
      match List.find_all (fun v' -> Id.eq v' v) env with
      | [id'] ->
        assert (id'.ty = TInt);
        TInt
      | _ -> assert false
    end
    | Op (_, args) ->
      List.iter (fun arg ->
        let ty = go_arith env arg in
        assert (ty = TInt);
      ) args;
      TInt
  in
  go env phi

let check_thflz_type rules rec_flags =
  let filter_global_env rules rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    List.filter_map
      (fun {outer; inner; _} ->
        let x = Id.remove_ty outer.var in
        match List.find_opt (fun (x', _) -> Id.eq x x') nids with
        | Some (_, Recursive) ->
          Some (inner.var)
        | Some (_, NotRecursive) ->
          Some (outer.var)
        | None -> None
      )
      rules
  in
  List.iter
    (fun {outer; inner; body; _} ->
      let global_env = filter_global_env rules rec_flags outer.var in
      let args = inner.args in
      assert (get_thflz_type (global_env @ args) body = TBool)
    )
    rules
    
let rec subst_ptype ptype subst =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (p1, p2, f) -> begin
    TFunc (
      subst_ptype p1 subst,
      subst_ptype p2 subst, f)
  end

let is_occur id ty =
  let rec go (ty : ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TBool -> false
    | TFunc (p1, p2, _) -> go p1 || go p2 in
  go ty

let compose_subst (id, ty) subst =
  let ty' = subst_ptype ty subst in
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
  let subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair], subst_ptype p2 [pair])) xs in
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
  print_endline "constraints:";
  print_endline @@ (Hflmc2_util.show_pairs show_ptype show_ptype constraints);
  let r = unify constraints in
  print_endline "unified:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_ptype r);
  print_endline "new flag_constraints:";
  print_endline @@ (Hflmc2_util.show_list show_enter_flag_constraint !flag_constraints);
  r, !flag_constraints

(* TODO: IDを共通化？ => 再帰のときのフラグを別途持たせる？その場合、元の引数との関連はどうなるのか？ *)
let remove_argument_flags ty =
  let rec go ty = match ty with
    | TFunc (ty1, ty2, f) -> begin
      let f =
        match f with
        | Enter -> EFVar (Id.gen ())
        | f -> f
      in
      TFunc (ty1, go ty2, f)
    end
    | _ -> ty
  in
  go ty
  
let to_thflzs hes is_recursive rec_flags =
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
      Abs (x, go (Env.update [x] env) p, TVar (Id.gen ()))
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
        let arg_and_flags =
          List.map (fun arg -> { arg with Id.ty = TVar (Id.gen ())}, EFVar (Id.gen ())) args in
        let outer =
          let rec go args = match args with
            | [] -> TBool
            | (x, f)::xs ->
              let flag =
                match fix with
                | Greatest -> f
                | Least -> begin
                  let (_, rec_f) = List.find (fun (id, _) -> Id.eq id var) is_recursive in
                  if rec_f then Enter
                  else f
                end
              in
              TFunc (x.Id.ty, go xs, flag)
          in 
          {var={var with ty = go arg_and_flags}; args = List.map (fun (arg, _) -> arg) arg_and_flags}
        in
        let inner =
          let rec go args = match args with
            | [] -> TBool
            | (x, f)::xs ->
              TFunc (x.Id.ty, go xs, f)
          in
          {var={var with ty=go arg_and_flags}; args = List.map (fun (arg, _) -> arg) arg_and_flags}
        in
        ( outer, inner, body, fix )
      )
      hes in
  let filter_global_env rules rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    Env.create @@
    List.filter_map
      (fun (outer, inner, _, _) ->
        let x = Id.remove_ty outer.var in
        match List.find_opt (fun (x', _) -> Id.eq x x') nids with
        | Some (_, Recursive) ->
          Some (inner.var)
        | Some (_, NotRecursive) ->
          Some (outer.var)
        | None -> None
      )
      rules
  in
  List.map
    (fun (outer, inner, body, fix) ->
      let global_env = filter_global_env rules rec_flags outer.var in
      let body = go (Env.update inner.args global_env) body in
      { outer; inner; body; fix }
    )
    rules
  
let generate_constraints (rules : ptype thes_rule list) (rec_flags : ('a Type.ty Id.t * ('a Type.ty Id.t * recursive_flag) list) list) : (ptype * ptype) list * enter_flag_constraint list =
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
    | Abs (arg, body, ty_aux) -> begin
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, c, f = gen env body in
      let ty = TFunc (arg.Id.ty, t, EFVar flag) in
      (ty, (ty, ty_aux) :: c, f)
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
      let (t2, c2, f2), flag_constrs = (
        let fvs = get_free_variables p2 in
        let env' = filter_env env fvs in
        let flag_constrs =
          Env.to_list env' |> List.map (fun id -> snd id.Id.ty)
          |> List.map (fun f -> EF_Le (EFVar flag_a1, f)) in
        (* if List.length flag_constrs > 0 then (
          print_endline "fvs";
          print_endline @@ Hflmc2_util.show_list Id.to_string fvs;
          print_endline "env'";
          print_endline @@ Env.show_env (fun id -> Id.to_string id) env';
          print_endline "flag_constrs";
          print_endline @@ 
            Hflmc2_util.fmt_string
              (Print_temp.hflz pp_ptype) raw;
          print_endline @@ Hflmc2_util.show_list show_enter_flag_constraint flag_constrs
        ); *)
        gen env' p2, flag_constrs ) in
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
    List.map (fun {outer; inner; _} -> (outer, inner, EFVar (Id.gen ()))) rules in
  let filter_global_env global_env rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    Env.create @@
    List.filter_map
      (fun (outer, inner, var_flag) ->
        let x = Id.remove_ty outer.var in
        match List.find_opt (fun (x', _) -> Id.eq x x') nids with
        | Some (_, Recursive) ->
          Some {inner.var with ty=(inner.var.ty, var_flag)}
        | Some (_, NotRecursive) ->
          Some {outer.var with ty=(outer.var.ty, var_flag)}
        | None -> None
      )
      global_env
  in
  List.map
    (fun { outer; inner; body; fix=_fix } ->
      let global_env = filter_global_env global_env rec_flags outer.var in
      let flags =
        let rec go ty = match ty with
          | TFunc (_, ty, f) -> f :: (go ty)
          | _ -> []
        in
        go inner.var.Id.ty
      in
      let args = List.map (fun (arg, flag) -> {arg with Id.ty=(arg.Id.ty, flag)}) (List.combine inner.args flags) in
      let _, constraints, flag_constraints = gen (Env.update args global_env) body in
      (constraints, flag_constraints)
    )
    rules
  |> List.split
  |> (fun (a, b) -> List.flatten a, List.flatten b)

let rec subst_ptype_and_subst_flag ptype subst subst_flags =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> subst_ptype_and_subst_flag v [] subst_flags
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (p1, p2, f) -> begin
    let f =
      match f with
      | EFVar id -> begin
        match List.find_opt (fun (k, _) -> Id.eq k id) subst_flags with
        | Some (_, v) -> begin
          match v with
          | EFVar _ -> NotEnter
          | v -> v
        end
        | None -> NotEnter
      end
      | f -> f in
    TFunc (
      subst_ptype_and_subst_flag p1 subst subst_flags,
      subst_ptype_and_subst_flag p2 subst subst_flags, f)
  end
  
  
let subst_program (rules : ptype thes_rule list) (subst : (unit Id.t * ptype) list) (subst_flags : (unit Id.t * enter_flag) list) =
  let subst_ptype ty subst subst_flags =
    (* print_endline "subst_ptype 1";
    print_endline @@ show_ptype ty;
    print_endline @@ Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_flags; *)
    subst_ptype_and_subst_flag ty subst subst_flags in
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var { v with ty = subst_ptype v.ty subst subst_flags }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p, ty_aux) -> Abs ({ v with Id.ty = subst_ptype v.Id.ty subst subst_flags }, go p, subst_ptype ty_aux subst subst_flags)
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
  List.map (fun {outer = outer; inner = inner; body; fix} ->
    let subst_var_args {var; args} =
      let var = { var with Id.ty = subst_ptype var.Id.ty subst subst_flags } in
      let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst subst_flags }) args in
      {var; args} in
    let outer = subst_var_args outer in
    let inner = subst_var_args inner in
    let body = go body in
    { outer; inner; body; fix }
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
    | Abs (v, p, _) -> Abs ({ v with ty = to_argty v.ty }, go p)
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
  List.map (fun {outer; inner = _inner; body; fix} ->
    let {var; args} = outer in
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
  print_endline "flag_constraints (to solve):";
  print_endline @@ (Hflmc2_util.show_list show_enter_flag_constraint constraints);
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
    | (Enter, Enter)::determined ->
      go_les_sub determined les
    | (NotEnter, NotEnter)::determined ->
      go_les_sub determined les
    | (_, _)::_ -> (* print_endline @@ Hflmc2_util.show_pairs show_enter_flag show_enter_flag determined; *) assert false
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
  (* print_endline "flag_constraints (subst_acc):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc);
  print_endline "flag_constraints (subst_acc'):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc');
  print_endline "flag_constraints (subst_acc''):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc'');
  print_endline "flag_constraints (composed):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed); *)
  (* print_endline "flag_constraints (solved):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed); *)
  composed
  
let infer_thflz_type (rules : ptype thes_rule list) rec_flags: ptype thes_rule list =
  let constraints, flag_constraints = generate_constraints rules rec_flags in
  let substitution, flag_constraints' = unify constraints in
  let flag_substitution = unify_flags (flag_constraints @ flag_constraints') in
  let rules = subst_program rules substitution flag_substitution in
  rules

let get_recursivity (rules : 'a Type.ty Hflz.hes_rule list) =
  let preds, graph = Hflz_util.get_dependency_graph rules in
  List.map
    (fun (i, pred) ->
      let reachables = Mygraph.reachable_nodes_from ~start_is_reachable_initially:false i graph in
      match List.find_opt (fun r -> r = i) reachables with
      | Some _ -> (pred, true)
      | None -> (pred, false)
    )
    preds
  
let construct_recursion_flags (rules : 'a Type.ty Hflz.hes_rule list) =
  let preds, graph = Hflz_util.get_dependency_graph rules in
  (* Depth first search *)
  let rec dfs seen current =
    let nids = Mygraph.get_next_nids current graph in
    (* 既に見たなら、「再帰」とフラグを付ける *)
    List.map
      (fun nid ->
        match List.find_opt (fun s -> s = nid) seen with
        | Some _ -> [(current, (nid, Recursive))]
        | None ->
          let map = dfs (nid::seen) nid in
          (current, (nid, NotRecursive)) :: map
      )
      nids
    |> List.flatten
  in
  let map = dfs [0] 0 in
  let map =
    Hflmc2_util.group_by (fun (key, _) -> key) map
    |> Hflmc2_util.list_of_hashtbl
    |> List.map (fun (k, vs) -> (k, List.map snd vs)) in
  let map =
    List.map
      (fun (k, flags) ->
        let flags =
          Hflmc2_util.group_by (fun (key, _) -> key) flags
          |> Hflmc2_util.list_of_hashtbl
          |> List.map (fun (k, vs) -> (k, List.map snd vs)) in
        let flag =
          List.map
            (fun (nid, flags) ->
              match List.find_opt (fun f -> match f with NotRecursive -> true | Recursive -> false) flags with
              | Some _ -> (nid, NotRecursive)
              | None -> (nid, Recursive)
            )
            flags in
        (k, flag)
      )
      map
  in
  let map =
    List.map
      (fun (i, id) ->
        match List.find_opt (fun (j, _) -> i = j) map with
        | Some (_, nids) ->
          (id, List.map (fun (k, v) -> let (_, id) = List.find (fun (i, _) -> i = k) preds in (id, v)) nids)
        | None -> (id, [])
      )
      preds
  in
  print_endline "recursion flags:";
  print_endline @@ Hflmc2_util.show_pairs Id.to_string (fun flags -> Hflmc2_util.show_pairs Id.to_string show_recursive_flag flags) map;
  map

let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let is_recursive = get_recursivity rules in
  let rec_flags = construct_recursion_flags rules in
  let rules = to_thflzs rules is_recursive rec_flags in
  print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules;
  let rules = infer_thflz_type rules rec_flags in
  let () =
    print_endline "result:";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    check_thflz_type rules rec_flags
    in
  print_endline "infer_thflz_type (2)";
  print_endline @@ show_s_thes_rules rules;
  let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  print_endline @@ Hflz.show_hes Type.pp_simple_ty hes; 
  hes
