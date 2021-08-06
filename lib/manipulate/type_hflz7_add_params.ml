open Hflmc2_syntax
open Type_hflz7_def

type ptype' = TInt' | TBool' | TFunc' of ptype' * ptype'
[@@deriving eq,ord]

let rec pp_ptype' prec ppf ty =
  match ty with
  | TBool' ->
    Fmt.pf ppf "bool"
  | TInt' ->
    Fmt.pf ppf "int"
  | TFunc' (ty1, ty2) ->
    Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a ->@ %a@]"
      (pp_ptype' Print.Prec.(succ arrow)) ty1
      (pp_ptype' Print.Prec.arrow) ty2

let show_ptype' = Hflmc2_util.fmt_string (pp_ptype' Print.Prec.zero) 

let get_thflz_type_without_check' phi =
  let rec go phi = match phi with
    | Bool _ -> TBool'
    | Var v -> v.ty
    | Or _ -> TBool'
    | And _ -> TBool'
    | Abs (_, _, lty) -> lty
    | Forall (_, body) -> go body
    | Exists (_, body) -> go body
    | App (p1, _) -> begin
      let ty1 = go p1 in
      match ty1 with
      | TFunc' (_, t2) -> t2
      | _ -> assert false
    end
    | Pred (_, _) -> TBool'
    | Arith _ -> TInt'
  in
  go phi

let show_pt_thflz body = 
  Hflmc2_util.fmt_string
    (Print_temp.hflz_ get_thflz_type_without_check' (fun _ -> "") pp_ptype') body

let print_pt_thflz body = print_endline @@ show_pt_thflz body

let should_add ty f =
  match ty with
  | TFunc _ -> begin
    match f with
    | TUse -> true
    | TNotUse -> false
    | EFVar _ -> assert false
  end
  | _ -> false

let rec convert_ty' ty : ptype' = match ty with
  | TFunc (argty, bodyty, f) -> begin
    if should_add argty f then
      TFunc' (TInt', TFunc' (convert_ty' argty, convert_ty' bodyty))
    else
      TFunc' (convert_ty' argty, convert_ty' bodyty)
  end
  | TBool -> TBool'
  | TInt -> TInt'
  | TVar _ -> assert false

let fold_formula f xs =
  match xs with
  | a::xs -> begin
    let rec go acc = function
      | x::xs -> go (f acc x) xs
      | [] -> acc
    in
    go a xs
  end
  | [] -> failwith "fold_formula: should have more than 0 elements"
  
let make_bounds xs c1 c2 r =
  let bounds =
    List.map
      (fun x ->
        (* r < (c1 * x) + c2, r < (-c1 * x) + c2 *)
        [ Pred (Lt, [Var r; (Op (Add, [(Op (Mult, [Int c1; Var x])); Int c2]))]);
          Pred (Lt, [Var r; (Op (Add, [(Op (Mult, [Int (-c1); Var x])); Int c2]))])]
      )
      xs
    |> List.concat in
  (bounds @ [Pred (Lt, [Var r; Int c2])]) |> fold_formula (fun acc f -> Or (acc, f))

(* check that a body of Abses has bool type *)
let check_t1 rules =
  let rec go phi = match phi with
    | Bool _ -> ()
    | Var _ -> ()
    | Or (p1, p2) ->
      go p1;
      go p2
    | And (p1, p2) ->
      go p1; go p2
    | Abs (_, phi, ty) -> begin
      match phi with
      | Abs _ -> ()
      | _ -> begin
        match ty with
        | TBool -> go phi
        | _ -> assert false
      end
    end
    | Forall (_, p) ->
      go p
    | Exists (_, p) ->
      go p
    | App (p1, p2) ->
      go p1;
      go p2
    | Arith _ -> ()
    | Pred _ -> ()
  in
  List.map (fun {body; _} -> go body) rules

let make_bounds' id_type_map add_args body =
  let rec go = function
    | (xs, c1, c2, r)::add_args ->      
      id_type_map := IdMap.add !id_type_map ({r with Id.ty=Type.TyInt}) (Hflz_util.VTVarMax (List.map (fun x -> {x with Id.ty=`Int}) xs));
      let bounds = make_bounds xs c1 c2 r in
      Forall (r, Or (bounds, go add_args))
    | [] ->
      body
  in
  go add_args

let make_bounds_if_body_is_bool id_type_map psi ty add_args =
  match ty with
  | TBool' ->
    make_bounds' id_type_map add_args psi
  | TFunc' _ -> begin
    if List.length add_args > 0 then assert false;
    psi
  end
  | TInt' -> assert false
  
let add_params c1 c2 rec_flags (rules : ptype thes_rule list) =
  let id_type_map = ref IdMap.empty in
  let rec go global_env rho phi = match phi with
    | Abs (x, psi, ty) -> begin
      let f =
        match ty with
        | TFunc (_, _, f) -> f
        | _ -> assert false in
      let will_add = should_add x.ty f in
      let x = { x with ty = convert_ty' x.ty } in
      if will_add then begin
        (* add param *)
        let k = id_gen ~name:"t" TInt' in
        let psi, ty, add_args = go global_env ((x, k)::rho) psi in
        let psi = make_bounds_if_body_is_bool id_type_map psi ty add_args in
        let ty = TFunc' (x.ty, ty) in
        let ty2 = TFunc' (TInt', ty) in
        id_type_map := IdMap.add !id_type_map k Hflz_util.VTHigherInfo;
        Abs (k, Abs (x, psi, ty), ty2), ty2, []
      end else begin
        let psi, ty, add_args = go global_env rho psi in
        let psi = make_bounds_if_body_is_bool id_type_map psi ty add_args in
        let ty = TFunc' (x.ty, ty) in
        Abs (x, psi, ty), ty, []
      end
    end
    | App (p1, p2) -> begin
      let ty1 = get_thflz_type_without_check p1 in
      let argty, f =
        match ty1 with
        | TFunc (argty, _, f) -> argty, f
        | _ -> assert false in
      let p1, ty1, add_args1 = go global_env rho p1 in
      let p2, ty2, add_args2 = go global_env rho p2 in
      let will_add = should_add argty f in
      if will_add then begin
        (* add arg *)
        let xs =
          let fvs = get_free_variables p2 in
          List.filter_map
            (fun fv ->
              match fv.Id.ty with
              | TInt' -> Some fv
              | TFunc' _ -> begin
                match List.find_opt (fun (id, _) -> Id.eq id fv) rho with
                | Some (_, i) -> Some i
                | None -> None
              end
              | TBool' -> None
            )
            fvs
          in
        let bodyty =
          match ty1 with
          | TFunc' (argty, bodyty) -> begin
            assert (argty = TInt');
            match bodyty with
            | TFunc' (argty, bodyty) ->
              assert (argty = ty2);
              bodyty
            | _ -> assert false
          end
          | _ -> assert false in
        let r = id_gen ~name:"s" TInt' in
        App (App (p1, Arith (Var r)), p2), bodyty, ((xs, c1, c2, r) :: add_args1 @ add_args2)
      end else begin
        let bodyty =
          match ty1 with
          | TFunc' (argty, bodyty) -> begin
            assert (argty = ty2);
            bodyty
          end
          | _ -> assert false in
        App (p1, p2), bodyty, add_args1 @ add_args2
      end
    end
    | Var v -> begin
      match List.find_opt (fun (id, _, _) -> Id.eq id v) global_env with
      | Some (_, true, v') ->
        (* print_endline @@ "Var(before): " ^ Id.to_string v ^ ": " ^ show_ptype v.ty; *)
        (* 最小不動点の最初の出現（の可能性がある）ときは、eta-展開を一律で行う *)
        (* 外側（Tが多い方）で引数を受け取る *)
        let rec go ty ty' = match ty, ty' with
          | TFunc (argty, bodyty, f), TFunc (argty', bodyty', f') -> begin
            assert (f = TUse);
            let x = id_gen (convert_ty' argty) in
            let fst =
              if should_add argty f then begin
                let k = id_gen TInt' in
                (* TODO: *)
                (* id_type_map := IdMap.add !id_type_map k (VTVarMax [{x with ty=convert_ty x.ty}]); *)
                Some k
              end else None in
            let snd = should_add argty' f' in
            (fst, snd, x) :: (go bodyty bodyty')
          end
          | TBool, TBool -> []
          | TInt, TInt | TVar _, TVar _ -> assert false
          | _ -> assert false in
        (* go outer_ty inner_ty *)
        let params = go v.ty v'.Id.ty in
        let rec make_abs body params = match params with
          | (fst, _, x) :: xs -> begin
            let b, ty = make_abs body xs in
            let ty = TFunc' (x.Id.ty, ty) in
            match fst with
            | Some x' ->
              let ty2 = TFunc' (x'.Id.ty, ty) in
              Abs (x', Abs (x, b, ty), ty2), ty2
            | None -> Abs (x, b, ty), ty
          end
          | [] ->
            let ty = get_thflz_type_without_check' body in
            (* print_pt_thflz body;
            print_endline @@ "ty: " ^ show_ptype' ty; *)
            assert (ty = TBool');
            body, TBool' in
        let rec make_app body params = match params with
          | (fst, snd, x) :: xs -> begin
            if snd then begin
              let x' =
                match fst with
                | Some x' -> x'
                | None -> assert false in
              App (App (make_app body xs, Arith (Var x')), Var x)
            end else
              App (make_app body xs, Var x)
          end
          | [] -> body in
        let v' = { v' with ty = convert_ty' v'.ty} in
        (* print_endline "v'";
        print_endline @@ show_ptype' v'.ty; *)
        let b = make_app (Var v') (List.rev params) in
        let psi, ty'' = make_abs b params in
        (* print_endline @@ "Var(after): " ^ show_pt_thflz psi ^ ": " ^ show_ptype v.ty; *)
        assert (ty'' = convert_ty' v.ty);
        psi, ty'', []
      | Some (_, false, _) | None ->
        let ty = convert_ty' v.ty in
        Var {v with ty = ty}, ty, []
    end
    | Or (p1, p2) ->
      let p1, ty1, c1 = go global_env rho p1 in
      let p1 = make_bounds' id_type_map c1 p1 in
      let p2, ty2, c2 = go global_env rho p2 in
      let p2 = make_bounds' id_type_map c2 p2 in
      assert (ty1 = TBool' && ty2 = TBool');
      Or (p1, p2), TBool', []
    | And (p1, p2) ->
      let p1, ty1, c1 = go global_env rho p1 in
      let p1 = make_bounds' id_type_map c1 p1 in
      let p2, ty2, c2 = go global_env rho p2 in
      let p2 = make_bounds' id_type_map c2 p2 in
      assert (ty1 = TBool' && ty2 = TBool');
      And (p1, p2), TBool', []
    | Forall (x, p) ->
      let p, ty1, c1 = go global_env rho p in
      assert (ty1 = TBool');
      let p = make_bounds' id_type_map c1 p in
      Forall ({x with ty=convert_ty' x.ty}, p), TBool', []
    | Exists (x, p) ->
      let p, ty1, c1 = go global_env rho p in
      assert (ty1 = TBool');
      let p = make_bounds' id_type_map c1 p in
      Exists ({x with ty=convert_ty' x.ty}, p), TBool', []
    | Arith a -> Arith (go_arith a), TInt', []
    | Pred (op, ps) -> Pred (op, List.map go_arith ps), TBool', []
    | Bool b -> Bool b, TBool', []
  and go_arith a = match a with
    | Int i -> Int i
    | Var x -> Var {x with ty=TInt'}
    | Op (o, ps) -> Op (o, List.map go_arith ps)
  in
  let global_env = List.map (fun {var; _} -> var) rules in
  let filter_global_env global_env rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    Env.create @@
    List.filter_map
      (fun var ->
        match List.find_opt (fun (x', _) -> Id.eq var x') nids with
        | Some (_, Recursive) ->
          Some ({var with ty=var.ty.inner_ty}, Recursive)
        | Some (_, NotRecursive) ->
          Some ({var with ty=var.ty.outer_ty}, NotRecursive)
        | None -> None
      )
      global_env
  in
  let rules =
    List.map
      (fun {var; body; fix} ->
        (* global_env: (id, 最小不動点の最初の出現か否か, 最小不動点の内側での型) *)
        let global_env =  
          filter_global_env global_env rec_flags var
          |> List.map (fun (v, f) ->
            let {fix; var; _} = List.find (fun {var;_} -> Id.eq var v) rules in
            (v, fix = Least && f = NotRecursive, {var with ty=var.ty.inner_ty})
          ) in
        let body, ty, c = go global_env [] body in
        let body = make_bounds' id_type_map c body in
        (* assert (List.length c = 0); *)
        assert ((convert_ty' var.ty.inner_ty) = ty);
        let var = { var with ty = convert_ty' var.ty.inner_ty} in
        (var, body, fix)
      )
      rules in
  rules, !id_type_map

let rec convert_ty ty = match ty with
  | TFunc' (argty, bodyty) ->
    let x = id_gen (convert_argty argty) in
    Type.TyArrow (x, convert_ty bodyty)
  | TBool' -> TyBool ()
  | TInt' -> failwith "cannot convert TInt'"
and convert_argty ty = match ty with
  | TInt' -> Type.TyInt
  | TFunc' _ | TBool' ->
    TySigma (convert_ty ty)
  
let to_hes original_fixpoint_pairs rules =
  let rec go (phi : ptype' thflz) : unit Type.ty Hflz.t = match phi with
    | Var v ->
      (* print_endline @@ "to_hes VAR: " ^ v.name ^ "_" ^ string_of_int v.id; *)
      Var {v with ty = convert_ty v.ty}
    | Bool b -> Bool b
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, _) ->
      Abs ({x with ty = convert_argty x.ty}, go p)
    | Forall (x, p) ->
      Forall ({x with ty = convert_argty x.ty}, go p)
    | Exists (x, p) ->
      Exists ({x with ty = convert_argty x.ty}, go p)
    | App (p1, p2) ->
      App (go p1, go p2)
    | Arith a ->
      Arith (go_arith a)
    | Pred (p, ps) ->
      Pred (p, List.map go_arith ps)
  and go_arith a = match a with
    | Int i -> Int i
    | Var x ->  
      assert (x.ty = TInt');
      Var {x with ty=`Int}
    | Op (p, ps) ->
      Op (p, List.map go_arith ps)
  in
  List.map
    (fun (var, body, fix) ->
      let var = {var with Id.ty=convert_ty var.Id.ty} in
      let body = go body in
      let fix =
        match fix with
        | Greatest -> Fixpoint.Greatest
        | Least -> Fixpoint.Least
        | NonRecursive ->
          snd @@ List.find (fun (id, _) -> Id.eq id var) original_fixpoint_pairs
      in
      {Hflz.var; body; fix}
    )
    rules

(* 不動点ごとのabsと整数引数の対応を取る *)