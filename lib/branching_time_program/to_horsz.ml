open Hflmc2_syntax
open Horsz

module R = Raw_horsz

module Env = struct
open Hflmc2_syntax

type 'a elt = 'a Id.t
type 'a t = 'a elt list

(* https://stackoverflow.com/a/30634912/12976091 *)
let cons_uniq f xs x = if List.exists (f x) xs then xs else x :: xs
let remove_from_left f xs = List.rev (List.fold_left (cons_uniq f) [] xs)
let remove_dublicate (env : 'a t) = remove_from_left (Id.eq) env
let exists_duplication ids =
  List.length ids <> (List.length @@ remove_dublicate ids)
  
let lookup (key : 'b Id.t) (env : 'a t) : 'a Id.t =
  match List.find_all (fun e -> Id.eq e key) env with
  | [e] -> e
  | [] -> raise Not_found
  | _ -> failwith "multiple found"

let update ~(bounds : 'a Id.t list) ~(env : 'a t) : 'a t =
  if exists_duplication bounds then failwith "update duplicate 1";
  if exists_duplication env then failwith "update duplicate 2";
  let env' = List.filter (fun e -> not @@ List.exists (fun b -> Id.eq b e) bounds) env in
  bounds @ env'

let empty = []

let create bounds = update bounds empty

let remove ~(bounds : 'a Id.t list) ~(env : 'a t) : 'a t =
  List.filter (fun e -> not @@ List.exists (fun b -> Id.eq b e) bounds) env

let merge (envs : 'a t list) =
  envs |> List.flatten |> remove_dublicate
let to_list x = x

end

let to_hors_expr env terminals body =
  let module R = R in
  let rec go phi = match phi with
    | R.PVar (s, n) -> begin
      assert (n = None);
      match List.find_all (fun n -> s = n.Id.name) env with
      | [id] -> begin
        match id.ty with
        | Type.TySigma t -> PVar { id with ty = t }
        | _ -> failwith @@ "convert PVar 3. Type-mismatch: should not be int type (name=" ^ Id.to_string id ^ ")"
      end
      | [] -> begin
        match List.find_all (fun (n', i) -> s = n') terminals with
        | [(t, i)] -> begin
          (* TODO: terminalの部分適用 *)
          if i <> 0 then failwith @@ "illegal use of terminal: " ^ s;
          Terminal (t, [])
        end
        | [] -> failwith @@ "unbounded: " ^ s ^ "/ " ^ (List.map (fun (s, i) -> s ^ "->" ^ string_of_int i) terminals |> String.concat ", ")
        | _ -> assert false
      end
      | _ -> assert false
    end
    | PIf (p1, p2, p3) -> begin
      If (go_formula p1, go p2, go p3)
    end
    | PApp (p1, p2) -> begin
      (* terminal + arguments *)
      let r =
        let rec agg_args acc p = match p with
          | R.PApp (p1, p2) -> (agg_args (p2 :: acc) p1)
          | PVar (s, n) -> Some ((s, n), acc)
          | _ -> None in
        match agg_args [] phi with
        | None -> None
        | Some ((s, n), args) -> begin
          assert (n = None);
          (match List.find_all (fun (n', i) -> s = n') terminals with
          | [(t, ti)] -> begin
            assert (ti = List.length args);
            (* TODO: terminalの部分適用 *)
            let args = List.map go args in
            Some (Terminal (t, args))
          end
          | [] -> None
          | _ -> assert false)
        end
      in
      match r with
      | None -> begin
        (* argument is integer? *)
        let p1 = go p1 in
        if (
          match p2 with
          | AInt _ | AOp _ -> true
          | PVar (s, n) -> begin
            match List.find_all (fun n -> s = n.Id.name) env with
            | [id] -> begin
              match id.ty with
              | Type.TyInt -> true
              | _ -> false
            end
            | _ -> false
          end
          | _ -> false)
        then AppInt (p1, go_arith p2)
        else App (p1, go p2)
      end
      | Some r -> r
    end
    | AInt _ -> assert false
    | AOp _ -> assert false
    | Pred _ -> assert false
    | And _ -> assert false
    | Or _ -> assert false
  and go_arith phi = match phi with
    | R.PVar (s, n) -> begin
      assert (n = None);
      match List.find_all (fun n -> s = n.Id.name) env with
      | [id] -> begin
        match id.ty with
        | Type.TyInt -> AVar { id with ty = `Int }
        | _ -> failwith @@ "convert AVar 3. Type-mismatch: should be int type (name=" ^ Id.to_string id ^ ")"
      end
      | [] -> failwith @@ "unbounded: " ^ s
      | _ -> assert false
    end
    | AInt n -> Int n
    | AOp (op, xs) ->
      Op (op, List.map go_arith xs)
    | _ -> failwith "go_arith"
  and go_formula phi = match phi with
    | R.And (p1, p2) -> And (go_formula p1, go_formula p2)
    | Or (p1, p2) -> Or (go_formula p1, go_formula p2)
    | Pred (p, xs) -> Pred (p, List.map go_arith xs)
    | _ -> failwith "go_formula"
  in
  go body

type ptype = TUnit | TInt | TFunc of ptype * ptype | TVar of unit Hflmc2_syntax.Id.t | TBool
[@@deriving eq,ord,show]

let rec subst_ptype ptype subst =
  let open R in
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TUnit | TBool-> ptype
  | TFunc (p1, p2) -> TFunc (subst_ptype p1 subst, subst_ptype p2 subst)

let is_occur id ty =
  let rec go (ty : ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TUnit | TBool -> false
    | TFunc (p1, p2) -> go p1 || go p2 in
  go ty

let compose_subst (id, ty) subst =
  let ty' = subst_ptype ty subst in
  (id, ty') :: subst
  
let unify (constraints : (ptype * ptype) list) =
  let open R in
  let is_equal_ptype = (=) in
  let rec subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair], subst_ptype p2 [pair])) xs in
  let rec unify constraints = match constraints with
    | [] -> []
    | (t1, t2)::xs -> begin
      if is_equal_ptype t1 t2
      then unify xs
      else begin
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
  print_endline @@ (show_pairs show_ptype show_ptype constraints); *)
  let r = unify constraints in
  (* print_endline "unify:";
  print_endline @@ (show_pairs Id.to_string show_ptype r); *)
  r

let rec to_ptype_from_ty = function
  | Type.TyBool _ -> TUnit
  | Type.TyArrow (ar, bo) -> TFunc (to_ptype_from_argty ar.ty, to_ptype_from_ty bo)
and to_ptype_from_argty = function
  | Type.TySigma (s) -> to_ptype_from_ty s
  | Type.TyInt -> TInt

let generate_constraints (terminals : (terminal * int) list) (raw : R.raw_program) :  
    (ptype * ptype) list *
    (ptype Id.t * ptype Id.t list * Raw_horsz.raw_expression) list =
  let open R in
  let terminals = 
    terminals
    |> List.map (fun (t, arity) ->
      let rec go = function 
        | 0 -> TUnit
        | i -> TFunc (TUnit, go (i - 1)) in
      let ty = go arity in
      { Id.name = t; id = 0; ty = ty }
    )
    |> Env.create in
  let rec gen (env : ptype Env.t) (raw : R.raw_expression):
      ptype * (ptype * ptype) list
       = match raw with
    | PIf (p1, p2, p3) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let t3, c3 = gen env p3 in
      (t2, [(t1, TBool); (t2, t3)] @ c1 @ c2 @ c3)
    | PApp (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar)) :: c1 @ c2)
    | AInt _ -> (TInt, [])
    | PVar (name, o) -> begin
      assert (o = None);
      let id =
        try
          Env.lookup {name=name; id=0; ty=()} env
        with Not_found -> Env.lookup {name=name; id=0; ty=()} terminals in
      (id.ty, [])
    end
    | AOp (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | Pred (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | And (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | Or (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2) in
  let raw =
    List.map
      (fun {var; args; body} ->
        let args =
          List.map (fun (name, ty) ->
            let ty =
              match ty with
              | None -> TVar (Id.gen ())
              | Some ty -> to_ptype_from_argty ty in
            { Id.name = name; id = 0; ty = ty }
          ) args in
        let rec go b = function
          | [] -> b
          | x::xs -> TFunc(x.Id.ty, go b xs) in
        let (var, o) = var in
        assert (o = None);
        let var_ty = go TUnit args in
        ({Id.name = var; id = 0; ty = var_ty} , args, body)
      )
      raw in
  let global_env =
    List.map
      (fun (var, _, _) ->
        var
      ) raw in
  let constraints =
    List.map
      (fun (var, args, body)-> 
        gen (Env.update args (Env.create global_env)) body |> snd
      )
      raw
    |> List.flatten in
  constraints, raw

let rec to_ty_from_ptype = function
  | TInt -> failwith "to_ty_from_ptype (TInt)"
  | TBool -> failwith "to_ty_from_ptype (TBool)"
  | TVar _ -> failwith "to_ty_from_ptype (TVar)"
  | TFunc (ty1, ty2) -> Type.TyArrow ({name = ""; id = 0; ty = to_argty_from_ptype ty1}, to_ty_from_ptype ty2)
  | TUnit -> Type.TyBool ()
and to_argty_from_ptype ty = match ty with
  | TInt -> Type.TyInt
  | TBool -> failwith "to_ty_from_ptype (TBool)"
  | TVar _ -> failwith "to_ty_from_ptype (TVar)"
  | TFunc _ -> Type.TySigma (to_ty_from_ptype ty)
  | TUnit -> Type.TySigma (to_ty_from_ptype ty)

let subst_program
    (raw : (ptype Id.t * ptype Id.t list * Raw_horsz.raw_expression) list)
    (subst : (unit Id.t * ptype) list) =
  let open R in
  let rec go (raw : R.raw_expression) = match raw with
    | AInt i -> AInt i
    | PVar (v, o) ->
      assert (o = None);
      PVar (v, None)
    | PIf (p1, p2, p3) -> PIf (go p1, go p2, go p3)
    | PApp (p1, p2) -> PApp (go p1, go p2)
    | AOp (o, ps) -> AOp (o, List.map go ps)
    | Pred (o, ps) -> Pred (o, List.map go ps)
    | And (p1, p2) -> And (go p1, go p2)
    | Or (p1, p2) -> Or (go p1, go p2)
    in
  List.map (fun (var, args, body) ->
    let var = (var.Id.name, Some (subst_ptype var.Id.ty subst |> to_argty_from_ptype)) in
    let args = List.map (fun v -> (v.Id.name, Some (subst_ptype v.Id.ty subst |> to_argty_from_ptype)) ) args in
    let body = go body in
    { R.var; args; body }
  ) raw
     
let infer_type terminals (raw : R.raw_program) =
  let constraints, raw = generate_constraints terminals raw in
  let substitution = unify constraints in
  let raw = subst_program raw substitution in
  raw
  
let to_horsz (terminals : (terminal * int) list) (raw : R.raw_program) =
  let module R = R in
  print_endline @@ R.show_raw_program raw;
  let raw = infer_type terminals raw in
  let (first, rules) =
    match raw with
    | first::rules -> begin
      let {R.var; args; body} = first in
      if List.length args <> 0 then failwith "first rule should not have arguments";
      (body, rules)
    end
    | [] -> failwith "no HORSz rules" in
  let rules =
    List.map (fun {R.var; args; body} ->
      let (name, ty) = var in
      let args =
        List.map (fun (s, ty) ->
          match ty with
          | None -> assert false
          | Some ty -> Id.gen ~name:s ty
        ) args in
      let ty = match ty with Some (Type.TySigma ty) -> ty | _ -> assert false in
      let v = Id.gen ~name:name ty in
      (v, args, body)
    ) rules in
  let global_env = List.map (fun (v, _, _) -> { v with Id.ty = Type.TySigma v.Id.ty }) rules in
  let entry = to_hors_expr global_env terminals first in
  let rules =
    List.map (fun (v, args, body) ->
      let env = global_env @ args in
      if Hflmc2_util.contains_duplicates (List.map (fun id -> id.Id.name) env @ (List.map fst terminals)) then
        failwith "arguments, terminal and nonterminal name conflict";
      let body = to_hors_expr env terminals body in
      {var = v; args; body}
    ) rules in
  (entry, rules)
  