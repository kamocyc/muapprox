open Hflmc2_syntax
module Env = Env_no_value
(* open Hflz *)

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type 'ty thflz =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty thflz * 'ty thflz
  | And    of 'ty thflz * 'ty thflz
  | Abs    of 'ty Id.t * 'ty thflz * 'ty
  | Forall of 'ty Id.t * 'ty thflz * 'ty
  | Exists of 'ty Id.t * 'ty thflz * 'ty
  | App    of 'ty thflz * 'ty thflz * 'ty
  | Arith  of 'ty tarith
  | Pred   of Formula.pred * 'ty tarith list
  [@@deriving eq,ord,show]

type enter_flag = Enter | NotEnter | EFVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type ptype = TInt | TBool | TFunc of ptype * ptype * enter_flag | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type 'a thes_rule = {var: 'a Id.t; args: 'a Id.t list; body: 'a thflz; fix: Fixpoint.t}
[@@deriving eq,ord,show]

type s_thes_rules = ptype thes_rule list
[@@deriving eq,ord,show]

type enter_flag_constraint = EF_Equal of enter_flag * enter_flag | EF_Le of enter_flag * enter_flag
[@@deriving eq,ord,show]

type recursive_flag = Recursive | NotRecursive
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
        Fmt.pf ppf "(%a : %a)" id x (format_ty_ Prec.zero) x.ty
        (* Fmt.pf ppf "%a" id x *)
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
      (* | Abs (x, psi, ty) -> begin
          let f_str = 
            match ty with
            | TFunc (_, _, f) -> show_enter_flag f
            | _ -> "" in
          show_paren (prec > Prec.abs) ppf "@[<1>λ%a:_{%s}%a.@,%a@]"
            id x
            f_str
            (format_ty_ Prec.(succ arrow)) x.ty
            (hflz_ format_ty_ Prec.abs) psi
      end *)
      | Abs (x, psi, ty) ->
        show_paren (prec > Prec.abs) ppf "@[<1>(λ%a:%a.@,%a)_{%a}@]"
            id x
            (format_ty_ Prec.(succ arrow)) x.ty
            (hflz_ format_ty_ Prec.abs) psi
            (format_ty_ Prec.(succ arrow)) ty
      | Forall (x, psi, _ty) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | Exists (x, psi, _ty) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      (* | App (psi1, psi2) -> begin
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
      end *)
      | App (psi1, psi2, ty) -> begin
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (hflz_ format_ty_ Prec.app) psi1
            (* (format_ty_ Prec.(succ arrow)) ty *)
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
    fun format_ty_ ppf {var; args; body; fix} ->
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
  
end

let dummy_flag = EFVar (Id.gen ())

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

let get_free_variables phi =
  let rec go phi = match phi with
    | Bool _ -> []
    | Var v -> [v]
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Forall (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Exists (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | App (p1, p2, _) -> go p1 @ go p2
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
    | Forall (x, body, ty) ->
      let ty' = go (x::env) body in
      assert (ty = ty');
      ty
    | Exists (x, body, ty) ->
      let ty' = go (x::env) body in
      assert (ty = ty');
      ty
    | App (p1, p2, ty) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      match ty1 with
      | TFunc (t1, t2, _) -> begin
        assert (t1 = ty2);
        assert (t2 = ty);
        ty
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

let rec subst_ptype ptype subst =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (p1, p2, f) -> TFunc (subst_ptype p1 subst, subst_ptype p2 subst, f)

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
  let is_equal_ptype = (=) in
  let subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair], subst_ptype p2 [pair])) xs in
  let rec unify constraints = match constraints with
    | [] -> []
    | (t1, t2)::xs -> begin
      if is_equal_ptype t1 t2
      then unify xs
      else begin
        (* print_endline "unify2";
        print_endline @@ Hflmc2_util.show_pairs show_ptype show_ptype (constraints); *)
        match t1, t2 with
        | TFunc (t11, t12, _), TFunc (t21, t22, _) ->
          unify ((t11, t21) :: (t12, t22) :: xs)
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
  (* print_endline "unify:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_ptype r); *)
  r

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
      Abs (x, go (Env.update [x] env) p, TVar (Id.gen ()))
    | Forall (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Forall (x, go (Env.update [x] env) p, TVar (Id.gen ()))
    | Exists (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Exists (x, go (Env.update [x] env) p, TVar (Id.gen ()))
    | App (p1, p2) ->
      App (go env p1, go env p2, TVar (Id.gen ()))
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
          | x::xs -> TFunc (x.Id.ty, go base xs, dummy_flag)
        in 
        ( {var with ty = go TBool args}, args, body, fix )
      )
      hes in
  let global_env = List.map (fun (var, _, _, _) -> var) rules |> Env.create in
  List.map
    (fun (var, args, body, fix) ->
      let body = go (Env.update args global_env) body in
      {var; args; body; fix}
    )
    rules

let generate_constraints (rules : ptype thes_rule list) : (ptype * ptype) list =
  let rec gen (env : ptype Env.t) (raw : ptype thflz)
      : ptype * (ptype * ptype) list = match raw with
    | Bool _ -> (TBool, [])
    | Var v ->
      let id = Env.lookup v env in
      (id.ty, [])
    | Or (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | And (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | Abs (arg, body, v) ->
      let t, c = gen (Env.update [arg] env) body in
      let ty = TFunc (arg.Id.ty, t, dummy_flag) in
      (ty, (ty, v) :: c)
    | Forall (arg, body, v) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (* (arg.Id.ty, TInt) :: *) (t, v) :: c)
    | Exists (arg, body, v) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (* (arg.Id.ty, TInt) :: *) (t, v) :: c)
    | App (p1, p2, v) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar, dummy_flag)) :: (TVar tvar, v) :: c1 @ c2)
    | Arith a ->
      let ty, c = gen_arith env a in
      (TInt, (TInt, ty) :: c)
    | Pred (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
  and gen_arith (env : ptype Env.t) (raw : ptype tarith)
      : ptype * (ptype * ptype) list = match raw with
    | Var v ->
      let id = Env.lookup v env in
      (id.ty, [(id.ty, TInt)])
    | Int _ -> (TInt, [])
    | Op (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    in
  let global_env = List.map (fun {var; _} -> var) rules in
  let constraints =
    List.map
      (fun { args; body; _ } ->
        gen (Env.update args (Env.create global_env)) body |> snd
      )
      rules
    |> List.flatten in
  constraints

let subst_program (rules : ptype thes_rule list) (subst : (unit Id.t * ptype) list) =
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var { v with ty = subst_ptype v.ty subst }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p, ty) -> Abs ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p, subst_ptype ty subst)
    | Forall (v, p, ty) -> Forall ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p, subst_ptype ty subst)
    | Exists (v, p, ty) -> Exists ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p, subst_ptype ty subst)
    | App (p1, p2, ty) -> App (go p1, go p2, subst_ptype ty subst)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Int i
    | Var v -> Var { v with ty = subst_ptype v.ty subst }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun {var; args; body; fix} ->
    let var = { var with Id.ty = subst_ptype var.Id.ty subst } in
    let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst }) args in
    let body = go body in
    {var; args; body; fix}
  ) rules

let rec get_flags_of_type ty =
  match ty with
  | TFunc (_, bodyty, f) -> f :: (get_flags_of_type bodyty)
  | _ -> []

let generate_subtype_constraint ty1 ty2 =
  let rec go ty1 ty2 =
    match ty1, ty2 with
    | TFunc (argty1, bodyty1, flag1), TFunc (argty2, bodyty2, flag2) ->
      (EF_Le (flag1, flag2)) :: (go argty2 argty1) @ (go bodyty1 bodyty2)
    | TBool, TBool -> []
    | TInt, TInt -> []
    | _ -> assert false
  in
  go ty1 ty2

let generate_type_equal_constraint ty1 ty2 =
  let rec go ty1 ty2 =
    match ty1, ty2 with
    | TFunc (argty1, bodyty1, flag1), TFunc (argty2, bodyty2, flag2) ->
      (EF_Equal (flag1, flag2)) :: (go argty1 argty2) @ (go bodyty1 bodyty2)
    | TBool, TBool -> []
    | TInt, TInt -> []
    | _ -> assert false
  in
  go ty1 ty2
  
let rec assign_flags_of_type ty =
  match ty with
  | TFunc (ty1, ty2, _) ->
    TFunc (assign_flags_of_type ty1, assign_flags_of_type ty2, EFVar (Id.gen ()))
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false

let assign_flags (rules : ptype thes_rule list) =
  let rec go env (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> begin
      match List.find_opt (fun v' -> Id.eq v v') env with
      | Some v ->
        Var v
      | None -> assert false
    end
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | And (p1, p2) -> And (go env p1, go env p2)
    | Abs (x, p1, ty) ->
      let x = {x with ty = assign_flags_of_type x.ty} in
      Abs (x, go (x :: env) p1, assign_flags_of_type ty)
    | Forall (x, p1, ty) ->
      let x = {x with ty = assign_flags_of_type x.ty} in
      Forall (x, go (x :: env) p1, assign_flags_of_type ty)
    | Exists (x, p1, ty) ->
      let x = {x with ty = assign_flags_of_type x.ty} in
      Exists (x, go (x :: env) p1, assign_flags_of_type ty)
    | App (p1, p2, ty) -> App (go env p1, go env p2, assign_flags_of_type ty)
    | Arith p -> Arith p
    | Pred (args, op) -> Pred (args, op)
  in
  let rules =
    List.map
      (fun {var; args; body; fix} ->
        let var = {var with ty=assign_flags_of_type var.ty} in
        let args = List.map (fun arg -> {arg with Id.ty=assign_flags_of_type arg.Id.ty}) args in
        (var, args, body, fix)
      )
      rules in
  let global_env = List.map (fun (var, _, _, _) -> var) rules in
  let rules =
    List.map
      (fun (var, args, body, fix) ->
        let body = go (global_env @ args) body in
        {var; args; body; fix}
      )
      rules in
  rules

let rec set_true_type ty =
  match ty with
  | TFunc (arg, body, _) -> TFunc (arg, set_true_type body, Enter)
  | TBool -> TBool
  | TInt -> TInt
  | _ -> assert false
  
let rec set_true_argument_types ty =
  match ty with
  | TFunc (arg, body, f) ->
    TFunc (set_true_type arg, set_true_argument_types body, f)
  | TBool -> TBool
  | TInt -> TInt
  | _ -> assert false

let generate_flag_constraints (rules : ptype thes_rule list) is_recursive rec_flags =
  let rec go env (phi : ptype thflz) = match phi with
    | App (phi1, phi2, ty) -> begin
      let ty1, c1 = go env phi1 in
      match ty1 with
      | TFunc (tyarg, tybody, flag) ->  
        let ty2, c2 = go env phi2 in
        let env2 = get_free_variables phi2 in
        let subtype_constrs = generate_subtype_constraint tyarg ty2 in
        let body_flag_constrs =
          get_flags_of_type tybody
          |> List.map (fun f -> EF_Le (f, flag)) in
        let env2_constrs =
          env2
          |> List.map (fun id -> get_flags_of_type id.Id.ty)
          |> List.flatten
          |> List.map (fun f ->
            get_flags_of_type ty2
            |> List.map (fun f' -> EF_Le (f', f))
          )
          |> List.flatten in
        ty, subtype_constrs @ body_flag_constrs @ env2_constrs @ c1 @ c2 @ (generate_type_equal_constraint tybody ty)
      | _ -> assert false
    end
    | Bool _ -> TBool, []
    | Var v -> begin
      match List.find_opt (fun v' -> Id.eq v v') env with
      | Some v' -> v'.ty, generate_type_equal_constraint v.ty v'.ty 
      | None -> assert false
    end
    | Or (phi1, phi2) ->
      let ty1, c1 = go env phi1 in
      let ty2, c2 = go env phi2 in
      assert (ty1 = TBool);
      assert (ty2 = TBool);
      TBool, c1 @ c2
    | And (phi1, phi2) ->
      let ty1, c1 = go env phi1 in
      let ty2, c2 = go env phi2 in
      assert (ty1 = TBool);
      assert (ty2 = TBool);
      TBool, c1 @ c2
    | Abs (x, phi, ty) -> begin
      match ty with
      | TFunc (ty1, ty2, _flag) -> begin
        let ty2', c1 = go (x::env) phi in
        let c = generate_type_equal_constraint ty1 x.ty in
        let c' = generate_type_equal_constraint ty2 ty2' in
        ty, c @ c' @ c1
      end
      | _ -> assert false
    end
    | Forall (x, phi, ty) ->
      let ty', c = go (x :: env) phi in
      ty, (generate_type_equal_constraint ty ty') @ c
    | Exists (x, phi, ty) ->
      let ty', c = go (x :: env) phi in
      ty, (generate_type_equal_constraint ty ty') @ c
    | Arith _ -> TInt, []
    | Pred _ -> TBool, []
  in
  List.map
    (fun {var; args; body; _} ->
      let global_env =
        let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
        List.filter_map
          (fun {var; _} ->
            let (_, rec_f) = List.find (fun (id, _) -> Id.eq id var) is_recursive in
            if not rec_f then Some var
            else begin
              let x = Id.remove_ty var in
              match List.find_opt (fun (x', _) -> Id.eq x x') nids with
              | Some (_, Recursive) ->
                Some (var)
              | Some (_, NotRecursive) ->
                Some ({var with ty = set_true_argument_types var.ty})
              | None -> None
            end
          )
          rules in
      let t, constrs = go (args @ global_env) body in
      assert (t = TBool);
      constrs
    )
    rules
  |> List.flatten
    
(* 
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
    | Abs (v, p, _) -> Abs ({ v with ty = to_argty v.ty }, go p)
    | Forall (v, p, _) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_equal_ctype v.Id.ty TInt);
        Forall ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | Exists (v, p, _) -> begin
      match v.Id.ty with
      | TVar _ -> go p
      | _ -> begin
        assert (is_equal_ctype v.Id.ty TInt);
        Exists ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | App (p1, p2, _) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Arith.Int i
    | Var v ->
      assert (is_equal_ctype v.ty TInt);
      Var { v with ty = `Int }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun {var; args; body; fix} ->
    let var = { var with Id.ty = to_ty var.Id.ty } in
    let args = List.map (fun v -> { v with Id.ty = to_argty v.Id.ty }) args in
    let body = go body in
    let rec go ls body = match ls with
      | [] -> body
      | x::xs -> Hflz.Abs (x, go xs body) in
    let body = go args body in
    { Hflz.var; body; fix }
  ) rules *)

let infer_thflz_type (rules : ptype thes_rule list): ptype thes_rule list =
  let constraints = generate_constraints rules in
  let substitution = unify constraints in
  let rules = subst_program rules substitution in
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
  print_endline "flag_constraints (subst_acc):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc);
  print_endline "flag_constraints (subst_acc'):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc');
  print_endline "flag_constraints (subst_acc''):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag subst_acc'');
  print_endline "flag_constraints (composed):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed);
  print_endline "flag_constraints (solved):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_enter_flag composed);
  composed

let rec subst_flags_type ty subst =
  match ty with
  | TFunc (ty1, ty2, f) -> begin
    let f =
      match f with
      | EFVar id -> begin
        match List.find_opt (fun (id', _) -> Id.eq id id') subst with
        | Some (_, f') -> f'
        | None -> f
      end
      | f -> f
      in
    TFunc (subst_flags_type ty1 subst, subst_flags_type ty2 subst, f)
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
  
let subst_flags_program (rules : ptype thes_rule list) (subst : (unit Id.t * enter_flag) list) : ptype thes_rule list =
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=subst_flags_type v.ty subst}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, ty) -> Abs ({x with ty=subst_flags_type x.ty subst}, go p, subst_flags_type ty subst)
    | Forall (x, p, ty) -> Forall ({x with ty=subst_flags_type x.ty subst}, go p, subst_flags_type ty subst)
    | Exists (x, p, ty) -> Exists ({x with ty=subst_flags_type x.ty subst}, go p, subst_flags_type ty subst)
    | App (p1, p2, ty) -> App (go p1, go p2, subst_flags_type ty subst)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var; args; body; fix} ->
      let var = { var with ty = subst_flags_type var.ty subst } in
      let args =
        List.map
          (fun arg -> { arg with Id.ty = subst_flags_type arg.Id.ty subst })
          args in
      let body = go body in
      { var; args; body; fix }
    )
    rules

let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let is_recursive = get_recursivity rules in
  let rec_flags = construct_recursion_flags rules in
  let rules = to_thflzs rules in
  (* print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = infer_thflz_type rules in
  print_endline "infer_thflz_type (1)";
  print_endline @@ show_s_thes_rules rules;
  let () =
    print_endline "result:";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    in
  let rules = assign_flags rules in
  let () =
    print_endline "result':";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    in
  let flag_constrs = generate_flag_constraints rules is_recursive rec_flags in
  let subst = unify_flags flag_constrs in
  let rules = subst_flags_program rules subst in
  let () =
    print_endline "result 2:";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    in
  (* TODO: to_hflz *)
  hes
  (* let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  (* print_endline @@ Hflz.show_hes Type.pp_simple_ty hes;  *)
  hes *)
