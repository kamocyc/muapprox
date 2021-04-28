open Hflmc2_syntax
module Env = Env_no_value
(* open Hflz *)

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type 'ty thflz =
  | Unit
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

type ptype = TInt | TBool | TUnit | TFunc of ptype * ptype | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type 'a thes_rule = ('a Id.t * 'a Id.t list * 'a thflz * Fixpoint.t)
[@@deriving eq,ord,show]

type s_thes_rules = ptype thes_rule list
[@@deriving eq,ord,show]

let rec show_ptype = function
  | TInt -> "int"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TFunc (p1, p2) -> "(" ^ show_ptype p1 ^ "->" ^ show_ptype p2 ^ ")"
  | TVar id -> Hflmc2_syntax.Id.to_string id
  
let rec subst_ptype ptype subst =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool | TUnit -> ptype
  | TFunc (p1, p2) -> TFunc (subst_ptype p1 subst, subst_ptype p2 subst)

let is_occur id ty =
  let rec go (ty : ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TBool | TUnit -> false
    | TFunc (p1, p2) -> go p1 || go p2 in
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
        | TFunc (t11, t12), TFunc (t21, t22) ->
          unify ((t11, t21) :: (t12, t22) :: constraints)
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

let to_thflzs hes dummy_unit_var_name =
  let rec go env (phi : 'a Hflz.t): ptype thflz = match phi with
    | Bool b -> Bool b
    | Var v ->
      if v.name = dummy_unit_var_name
      then Unit
      else begin
        let id = Env.lookup v env in
        Var id
      end
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
          | x::xs -> TFunc (x.Id.ty, go base xs)
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


let erase_thflz_type (rules : ptype thes_rule list) =
  let rec go env (phi : ptype thflz): ptype thflz = match phi with
    | Unit -> Unit
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
      (fun (var, args, body, fix) ->
        let args = List.map (fun arg -> { arg with Id.ty = TVar (Id.gen ())}) args in
        let rec go base ls = match ls with
          | [] -> base
          | x::xs -> TFunc (x.Id.ty, go base xs)
        in 
        ( {var with Id.ty = go TBool args}, args, body, fix )
      )
      rules in
  let global_env = List.map (fun (v, _, _, _) -> v) rules |> Env.create in
  List.map
    (fun (var, args, body, fix) ->
      let body = go (Env.update args global_env) body in
      ( var, args, body, fix )
    )
    rules
    
let generate_constraints (rules : ptype thes_rule list) : (ptype * ptype) list =
  let rec gen (env : ptype Env.t) (raw : ptype thflz)
      : ptype * (ptype * ptype) list = match raw with
    | Unit -> (TUnit, [])
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
    | Abs (arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (TFunc (arg.Id.ty, t), c)
    | Forall (arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (* (arg.Id.ty, TInt) :: *) c)
    | Exists (arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (* (arg.Id.ty, TInt) :: *) c)
    | App (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar)) :: c1 @ c2)
    | Arith a ->
      let ty, c = gen_arith env a in
      (TInt, (TInt, ty) :: c)
    | Pred (e, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
  and gen_arith (env : ptype Env.t) (raw : ptype tarith)
      : ptype * (ptype * ptype) list = match raw with
    | Var v ->
      let id = Env.lookup v env in
      (id.ty, [(id.ty, TInt)])
    | Int i -> (TInt, [])
    | Op (e, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    in
  let global_env = List.map (fun (v, _, _, _) -> v) rules in
  let constraints =
    List.map
      (fun ( var, args, body, fix ) ->
        gen (Env.update args (Env.create global_env)) body |> snd
      )
      rules
    |> List.flatten in
  constraints

let subst_program (rules : ptype thes_rule list) (subst : (unit Id.t * ptype) list) =
  let rec go (phi : ptype thflz) = match phi with
    | Unit -> Unit
    | Bool b -> Bool b
    | Var v -> Var { v with ty = subst_ptype v.ty subst }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p) -> Abs ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p)
    | Forall (v, p) -> Forall ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p)
    | Exists (v, p) -> Exists ({ v with Id.ty = subst_ptype v.Id.ty subst }, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : ptype tarith) = match phi with
    | Int i -> Int i
    | Var v -> Var { v with ty = subst_ptype v.ty subst }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun (var, args, body, fix) ->
    let var = { var with Id.ty = subst_ptype var.Id.ty subst } in
    let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst }) args in
    let body = go body in
    ( var, args, body, fix )
  ) rules

let rec to_ty = function
  | TFunc (arg, body) -> Type.TyArrow ({name = ""; id = 0; ty = to_argty arg}, to_ty body)
  | TBool -> Type.TyBool ()
  | TUnit -> Type.TyBool ()
  | TInt -> assert false
  | TVar _ -> assert false
and to_argty = function
  | TInt -> Type.TyInt
  | t -> Type.TySigma (to_ty t)
  
let to_hflz (rules : ptype thes_rule list) =
  let is_equal_ctype = (=) in
  let rec go (phi : ptype thflz) = match phi with
    | Unit -> failwith "to_hflz: unit value"
    | Bool b -> Hflz.Bool b
    | Var v -> Var { v with ty = to_ty v.ty }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (v, p) -> Abs ({ v with ty = to_argty v.ty }, go p)
    | Forall (v, p) -> begin
      match v.Id.ty with
      | TUnit | TVar _ -> go p
      | _ -> begin
        assert (is_equal_ctype v.Id.ty TInt);
        Forall ({ v with Id.ty = Type.TyInt }, go p)
      end
    end
    | Exists (v, p) -> begin
      match v.Id.ty with
      | TUnit | TVar _ -> go p
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

let dummy_unit_var_name = "DUMMY_UNIT_VAR"

let infer_thflz_type (rules : ptype thes_rule list): ptype thes_rule list =
  let constraints = generate_constraints rules in
  let substitution = unify constraints in
  let rules = subst_program rules substitution in
  rules
  
let infer_type (hes : 'a Hflz.hes) =
  let rules = Hflz.merge_entry_rule hes in
  let rules = to_thflzs rules dummy_unit_var_name in
  (* print_endline @@ show_s_thes_rules rules; *)
  let rules = infer_thflz_type rules in
  let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  hes

let eliminate_unit_type_terms (rules: ptype thes_rule list): ptype thes_rule list =
  (* TODO: 型推論時の型変数が残っているとき？ *)
  let rec go (phi : ptype thflz) =
    match phi with
    | Unit -> Unit (* ? *)
    | Bool b -> Bool b
    | Var v -> begin
      match v.ty with
      | TUnit -> Unit
      | _ -> Var v
    end
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p) -> begin
      let p = go p in
      match x.ty with
      | TUnit -> p
      | _ -> Abs (x, p)
    end
    | Exists (x, p) -> begin
      let p = go p in
      match x.ty with
      | TUnit -> p
      | _ -> Exists (x, p)
    end
    | Forall (x, p) -> begin
      let p = go p in
      match x.ty with
      | TUnit -> p
      | _ -> Forall (x, p)
    end
    | App (p1, p2) -> begin
      let p1 = go p1 in
      let p2 = go p2 in
      match p2 with
      | Unit -> p1
      | _ -> App (p1, p2)
    end
    | Arith p -> Arith p
    | Pred (e, ps) -> Pred (e, ps)
  in
  let rules =
    List.filter_map
      (fun (var, args, body, fix) ->
        let args = List.filter (fun arg -> arg.Id.ty <> TUnit) args in
        let body = go body in
        match body with
        | Unit -> None
        | body -> Some (var, args, body, fix)
      )
      rules in
  rules  


(* TODO: debug *)
let infer_and_eliminate_unit_type_terms (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let rules = to_thflzs rules dummy_unit_var_name in
  (* print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = infer_thflz_type rules in
  (* print_endline "infer_thflz_type (1)";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = eliminate_unit_type_terms rules in
  (* print_endline "eliminate_unit_type_terms";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = erase_thflz_type rules in
  let rules = infer_thflz_type rules in
  (* print_endline "infer_thflz_type (2)";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes;
  (* print_endline @@ Hflz.show_hes Type.pp_simple_ty hes;  *)
  hes
