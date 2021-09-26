open Hflmc2_syntax
module Env = Env_no_value

open Add_arguments_tuple

let generate_type_equal_constraint ty1 ty2 =
  let rec go ty1 ty2 =
    match ty1, ty2 with
    | TFunc (argtys1, bodyty1), TFunc (argtys2, bodyty2) ->
      (List.map
        (fun ((argty1, tag1), (argty2, tag2)) ->
          T.EF_Equal (tag1, tag2) :: go argty1 argty2
        )
        (List.combine argtys1 argtys2)
      |> List.flatten)
      @ (go bodyty1 bodyty2)
    | TBool, TBool -> []
    | TInt, TInt -> []
    | _ -> assert false
  in
  go ty1 ty2

let rec assign_flags_to_type (ty : ptype2) =
  match ty with
  | TFunc (tyargs, tybody) ->
    TFunc (
      List.map
        (fun (ty, t) ->
          assert (t = T.dummy_use_flag);
          assign_flags_to_type ty,
          T.EFVar (Id.gen ()))
        tyargs,
      assign_flags_to_type tybody
    )
  | TInt -> TInt
  | TBool -> TBool
  | TVar v -> TVar v

let assign_flags (rules : ptype2 thes_rule list) : ptype2 thes_rule_in_out list =
  let rec go (raw : ptype2 thflz2) : ptype2 thflz2 = match raw with
    | Bool b -> Bool b
    | Var v -> Var {v with ty = assign_flags_to_type v.ty}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty = assign_flags_to_type x.Id.ty}) xs, go p, assign_flags_to_type ty)
    | Forall (x, p) -> Forall ({x with ty=assign_flags_to_type x.ty}, go p)
    | Exists (x, p) -> Exists ({x with ty=assign_flags_to_type x.ty}, go p)
    | App (p1, ps) -> App (go p1, List.map go ps)
    | Arith a -> Arith a
    | Pred (e, ps) -> Pred (e, ps)
  in
  List.map
    (fun {var; body; fix} ->
      let inner_ty = assign_flags_to_type var.ty in
      let outer_ty =
        let rec go = function
          | TFunc (argty, bodyty) ->
            TFunc (
              List.map (fun (arg, _) -> arg, T.TUse) argty,
              go bodyty
            )
          | TBool -> TBool
          | _ -> assert false
        in
        go inner_ty
      in
      let var = {var with ty = {T.inner_ty; outer_ty}} in
      let body = go body in
      { var_in_out = var; body; fix}
    )
    rules

let get_global_env {var_in_out; body; _} outer_mu_funcs global_env =
  let lookup v env =
    List.find (fun (id, _) -> Id.eq id v) env |> snd in
  let env_has v env =
    match List.find_opt (fun v' -> Id.eq v' v) env with
    | Some _ -> true
    | None -> false
  in
  let current_outer_pvars = lookup var_in_out outer_mu_funcs in
  let global_preds =
    get_free_variables body
    |> List.filter (fun v -> Hflz_manipulate.is_pred v) in
  global_preds
  |> List.map (fun pvar ->
    let arg_pvars = lookup pvar outer_mu_funcs in
    let new_pvars =
      List.filter (fun pvar -> not @@ env_has pvar current_outer_pvars) arg_pvars in
    (* var_in_outと、追加するpredicateが一致しないことがある。しかし、どちらにせよその引数として渡されている値は最小不動点の中で使う可能性があるので、単にタグをTにすればよい *)
    let (pvar_e, tag) = List.find (fun (v, _) -> Id.eq v pvar) global_env in
    if new_pvars = [] then
      {pvar with ty=(pvar_e.ty.T.inner_ty, tag)}
    else
      {pvar with ty=(pvar_e.ty.outer_ty, tag)}
  )
  |> Env.create

let generate_flag_constraints
    (rules : ptype2 thes_rule_in_out list)
    (outer_mu_funcs : ('a Id.t * 'a Id.t list) list)
    : T.use_flag_constraint list =
  let filter_env env fvs =
    List.fold_left
      (fun env' fv ->
        let v = Env.lookup fv env in
        Env.update [v] env'
      )
      (Env.create [])
      fvs
  in
  let rec gen (env : (ptype2 * T.use_flag) Env.t) (raw : ptype2 thflz2)
      : ptype2 * T.use_flag_constraint list = match raw with
    | Bool _ -> (TBool, [])
    | Var v ->
      let id = Env.lookup v env in
      let ty, _ = id.ty in
      (ty, generate_type_equal_constraint ty v.ty)
    | Or (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool && t2 = TBool);
      (TBool, f1 @ f2)
    | And (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool && t2 = TBool);
      (TBool, f1 @ f2)
    | Abs (args, body, ty_aux) -> begin
      let arg_tags = List.map (fun arg -> (arg, T.EFVar (Id.gen ()))) args in
      let env = Env.update (List.map (fun (arg, tag) -> {arg with Id.ty = (arg.Id.ty, tag)}) arg_tags) env in
      let t, fc = gen env body in
      let ty = TFunc (List.map (fun (arg, tag) -> (arg.Id.ty, tag)) arg_tags, t) in
      (ty, (generate_type_equal_constraint ty_aux ty) @ fc)
    end
    | Forall (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, T.EFVar flag)}] env in
      let t, f = gen env body in
      (t, f)
    | Exists (arg, body) -> begin
      let t, f =
        let flag = Id.gen () in
        let env' = Env.update [{arg with ty = (arg.ty, T.EFVar flag)}] env in
        gen env' body in
      let flag_constrs =
        let fvs =
          get_free_variables body 
          |> List.filter (fun x' -> not @@ Id.eq x' arg) in
        let env' = filter_env env fvs in
        Env.to_list env'
        |> List.map (fun id -> snd id.Id.ty)
        |> List.map (fun f -> T.EF_Equal (f, TUse)) in        
      (t, f @ flag_constrs)
    end
    | App (p1, ps) -> begin
      let t1, f1 = gen env p1 in
      let tyargs, tybody =
        match t1 with
        | TFunc (tyargs, tybody) -> tyargs, tybody
        | _ -> assert false
      in
      let flag_constrs =
        (List.combine ps tyargs)
        |> List.map
          (fun (p2, (ty2, tag)) ->
            let fvs = get_free_variables p2 in
            let env' = filter_env env fvs in
            let flag_constrs =
              Env.to_list env'
              |> List.map (fun id -> snd id.Id.ty)
              |> List.map (fun f -> T.EF_Le (tag, f)) in
            let t2, f2 = gen env' p2 in
            f2 @ flag_constrs @ (generate_type_equal_constraint ty2 t2)
          )
        |> List.flatten
      in
      (tybody, f1 @ flag_constrs)
    end
    | Arith _ -> (TInt, [])
    | Pred _ -> (TBool, [])
  in
  let global_env =
    List.map (fun {var_in_out; _} -> (var_in_out, T.EFVar (Id.gen ()))) rules in
  List.map
    (fun ({ var_in_out; body; fix=_fix } as rule) ->
      let global_env =
        get_global_env rule outer_mu_funcs global_env
      in
      let ty, flag_constraints = gen global_env body in
      (generate_type_equal_constraint ty var_in_out.ty.inner_ty) @ flag_constraints
    )
    rules
  |> List.flatten

let rec subst_flags_type ty subst =
  let subst_flag f =
    match f with
      | T.EFVar id -> begin
        match List.find_opt (fun (id', _) -> Id.eq id id') subst with
        | Some (_, f') -> f'
        | None -> f
      end
      | f -> f
  in
  match ty with
  | TFunc (tys, ty2) -> begin
    TFunc (
      List.map
        (fun (ty1, tag) ->
          subst_flags_type ty1 subst,
          subst_flag tag
        )
        tys,
      subst_flags_type ty2 subst
    )
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
  
let subst_flags_program (rules : ptype2 thes_rule_in_out list) (subst : (unit Id.t * T.use_flag) list) : ptype2 thes_rule_in_out list =
  let rec go (phi : ptype2 thflz2) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=subst_flags_type v.ty subst}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty=subst_flags_type x.Id.ty subst}) xs, go p, subst_flags_type ty subst)
    | Forall (x, p) -> Forall ({x with ty=subst_flags_type x.ty subst}, go p)
    | Exists (x, p) -> Exists ({x with ty=subst_flags_type x.ty subst}, go p)
    | App (p1, p2) -> App (go p1, List.map go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var_in_out; body; fix} ->
      let var_in_out = { var_in_out with ty = {T.inner_ty = subst_flags_type var_in_out.ty.inner_ty subst; outer_ty = subst_flags_type var_in_out.ty.outer_ty subst }} in
      let body = go body in
      { var_in_out; body; fix }
    )
    rules

let rec set_tag_in_undetermined_tags_ty ty to_set_tag =
  match ty with
  | TFunc (argtys, bodyty) -> begin
    TFunc (
      List.map
        (fun (argty, tag) ->
          set_tag_in_undetermined_tags_ty argty to_set_tag,
          let tag =
            match tag with
            | T.EFVar _ -> to_set_tag
            | tag -> tag in
          tag
        )
        argtys,
      set_tag_in_undetermined_tags_ty bodyty to_set_tag
    )
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false

let set_tag_in_undetermined_tags rules to_set_tag =
  let rec go (phi : ptype2 thflz2) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=set_tag_in_undetermined_tags_ty v.ty to_set_tag}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty=set_tag_in_undetermined_tags_ty x.Id.ty to_set_tag}) xs, go p, set_tag_in_undetermined_tags_ty ty to_set_tag)
    | Forall (x, p) -> Forall ({x with ty=set_tag_in_undetermined_tags_ty x.ty to_set_tag}, go p)
    | Exists (x, p) -> Exists ({x with ty=set_tag_in_undetermined_tags_ty x.ty to_set_tag}, go p)
    | App (p1, p2) -> App (go p1, List.map go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var_in_out; body; fix} ->
      let var_in_out = { var_in_out with ty = {T.inner_ty = set_tag_in_undetermined_tags_ty var_in_out.ty.inner_ty to_set_tag; outer_ty = set_tag_in_undetermined_tags_ty var_in_out.ty.outer_ty to_set_tag}} in
      let body = go body in
      { var_in_out; body; fix }
    )
    rules

let infer_thflz_type
    (rules : ptype2 thes_rule list)
    (outer_mu_funcs : ('a Id.t * 'a Id.t list) list): ptype2 thes_rule_in_out list =
  let rules = assign_flags rules in
  let flag_constraints = generate_flag_constraints rules outer_mu_funcs in
  let flag_substitution = Add_arguments_unify_flags.unify_flags flag_constraints in
  let rules = subst_flags_program rules flag_substitution in
  let rules = set_tag_in_undetermined_tags rules T.TNotUse in
  rules

let set_use_tag (rules : ptype2 thes_rule list): ptype2 thes_rule_in_out list =
  let rules = assign_flags rules in
  let rules = set_tag_in_undetermined_tags rules T.TUse in
  rules

(* 
let show_id_map id_map show_f = 
  "{" ^
  (IdMap.to_alist id_map
  |> List.map (fun (id, vt) -> "" ^ Id.to_string id ^ "=" ^ show_f vt)
  |> String.concat ", ") ^
  "}"

module Print_temp = struct
  include Print_temp
  
  let hflz_hes_rule : (Print.Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf {var; body; fix} ->
      let args, body = get_args body in
      Fmt.pf ppf "@[<2>%s %a =%s@ %a@]"
        (Id.to_string var)
        (Print.pp_print_list
          ~pp_sep:Print_syntax.PrintUtil.fprint_space
          (fun ppf (args, tts) ->
            (* if !show_tag_as_separator then
              fprintf ppf "(%s : (%a){%s})" (Id.to_string arg) (format_ty_ Prec.zero) arg.Id.ty (show_use_flag f2)
            else *)
              Print.fprintf ppf "(%s : %s)"
                (show_list Id.to_string args)
                (Hflmc2_util.fmt_string pp_ptype2_arg tts)
              (* fprintf ppf "(%s : %a)" (Id.to_string arg) (format_ty_ Prec.zero) arg.Id.ty *)
          )
        )
        args
        (show_fixpoint fix)
        (hflz_ thflz_to_ptype format_ty_) body

  let hflz_hes :  (Print.Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
end *)
