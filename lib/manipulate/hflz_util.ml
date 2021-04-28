open Hflmc2_syntax
open Hflz

type variable_type =
  (* | VTOrdinal
  | VTRec *)
  | VTVarMax of [`Int] Id.t list
  | VTHigherInfo
[@@deriving show]

let lift_id id =
  { id with Id.ty = Type.TySigma id.Id.ty}

let unlift_id id =
  { id with Id.ty = Type.unsafe_unlift id.Id.ty}

let get_dependency_graph (hes : 'a hes_rule list) =
  let preds = List.mapi (fun i {var; _} -> (i, var)) hes in
  let graph_size = List.length hes in
  let graph = Mygraph.init graph_size in
  (* 参照の依存グラフを作成 *)
  List.iteri
    (fun index {body; _} -> 
      fvs body
      |> IdSet.to_list
      |> List.filter_map
        (fun v ->
          List.find_opt (fun (_, v') -> Id.eq v' v) preds
        )
      |> List.iter (fun (i', _) -> 
        Mygraph.add_edge index i' graph
      )
    )
    hes;
  preds, graph

let show_hflz hflz = show Type.pp_simple_ty hflz

let get_hflz_type phi =
  let open Type in
  let rec go phi = match phi with
    | Bool   _ -> TyBool ()
    | Var    v -> v.ty
    | Or (f1, f2)  -> begin
      assert ((go f1) = TyBool ());
      assert ((go f2) = TyBool ());
      TyBool ()
    end
    | And (f1, f2) -> begin
      assert ((go f1) = TyBool ());
      assert ((go f2) = TyBool ());
      TyBool ()
    end
    | Abs (x, f1)  -> TyArrow (x, go f1)
    | Forall (_, f1) -> go f1
    | Exists (_, f1) -> go f1
    | App (f1, f2)   -> begin
      let ty1 = go f1 in
      match ty1 with
      | TyArrow (x, ty1') -> begin
        (match x.ty with
        | TyInt -> (match f2 with Arith _ -> () | _ -> failwith @@ "Illegal type (App, Arrow) (ty1=TyInt, ty2=(not integet expression)) (expression: " ^ show_hflz phi ^ ")")
        | TySigma t -> (
          let sty2 = go f2 in
          if not @@ eq_modulo_arg_ids t sty2 then (
            failwith @@ "Type assertion failed (ty1=" ^ show_simple_ty t ^ ", ty2=" ^ show_simple_ty sty2 ^ ")"
          )
        )
        );
        ty1'
      end
      | _ -> failwith "Illegal type (App)"
      
    end
    | Pred _ -> TyBool ()
    | Arith _ -> failwith "Illegal type (Arith)"
  in
  go phi


open Hflmc2_syntax

let assign_unique_variable_id (hes : Type.simple_ty Hflz.hes_rule list): Type.simple_ty Hflz.hes_rule list =
  let to_ty ty = match ty with
    | Type.TyInt -> failwith "ty"
    | TySigma s -> s
  in
  let to_arithty ty = match ty with
    | Type.TyInt -> `Int
    | TySigma _ -> failwith "arithty"
  in
  let global_env =
    List.map (fun {Hflz.var; _} ->
      (Id.remove_ty var, {Id.name = var.name; id = Id.gen_id (); ty = Type.TySigma (var.Id.ty)})
    ) hes in
  let rec go env body = match body with
    | Hflz.Bool b -> Hflz.Bool b
    | Var v -> begin
      match List.find_all (fun (e, _) -> Id.eq e v) env with
      | [(_, v)] -> Var ({v with ty = to_ty v.Id.ty})
      | [] -> failwith @@ "unbound: " ^ Id.to_string v
      | _ -> assert false
    end
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | And (p1, p2) -> And (go env p1, go env p2)
    | Abs (x, p) ->
      let x' = { x with id = Id.gen_id () } in
      Abs (x', go ((Id.remove_ty x, x') :: env) p)
    | Forall (x, p) -> 
      let x' = { x with id = Id.gen_id () } in
      Forall (x', go ((Id.remove_ty x, x') :: env) p)
    | Exists (x, p) -> 
      let x' = { x with id = Id.gen_id () } in
      Exists (x', go ((Id.remove_ty x, x') :: env) p)
    | App (p1, p2) -> App (go env p1, go env p2)
    | Arith a -> Arith (go_arith env a)
    | Pred (e, ps) -> Pred (e, List.map (go_arith env) ps)
  and go_arith env a = match a with
    | Int i -> Int i
    | Var v -> begin
      match List.find_all (fun (e, _) -> Id.eq e v) env with
      | [(_, v)] -> Var ({v with ty = to_arithty v.Id.ty})
      | [] -> failwith @@ "unbound: " ^ Id.to_string v
      | _ -> assert false
    end
    | Op (o, ps) -> Op (o, List.map (go_arith env) ps)
  in
  List.map (fun {Hflz.var; body; fix} ->
    let body = go global_env body in
    let var =
      match List.find_all (fun (e, _) -> Id.eq e var) global_env with
      | [(_, v)] -> {v with ty = to_ty v.Id.ty}
      | [] -> failwith @@ "unbound: " ^ Id.to_string var
      | _ -> assert false
    in
    {Hflz.var; body; fix}
  ) hes


let with_rules f hes = hes |> merge_entry_rule |> f |> decompose_entry_rule


let rec beta (phi : 'a Hflz.t) : 'a Hflz.t = match phi with
  | Or (phi1, phi2) -> Or (beta phi1, beta phi2)
  | And(phi1, phi2) -> And(beta phi1, beta phi2)
  | App(phi1, phi2) -> begin
    let phi1, phi2 = beta phi1, beta phi2 in
    let reduced = ref false in
    let rec go acc phi1 = match phi1 with
      | Forall (x, phi1) -> Forall (x, go (x::acc) phi1)
      | Exists (x, phi1) -> Exists (x, go (x::acc) phi1)
      | Abs(x, phi1) -> begin
        let fvs = fvs_with_type phi2 in
        (* print_endline @@ Print_syntax.show_hflz phi1;
        print_endline "fvs:"; Hflmc2_util.print_list Id.to_string fvs;
        print_endline "acc:"; Hflmc2_util.print_list Id.to_string acc; *)
        if List.exists (fun a -> List.exists (fun v -> Id.eq a v) acc) fvs then failwith "[beta] free variable collision";
        reduced := true;
        beta @@ Trans.Subst.Hflz.hflz (IdMap.of_list [x, phi2]) phi1
      end
      | phi1 -> phi1 in
    let res = go [] phi1 in
    if !reduced then
      beta res
    else (
      (* Log.app begin fun m -> m ~header:"not done" "%a" Print.(hflz simple_ty_) (App (phi1, phi2)) end; *)
      App (phi1, phi2))
  end
  | Abs(x, phi) -> Abs(x, beta phi)
  | Forall (x, phi) -> Forall (x, beta phi)
  | Exists (x, phi) -> Exists (x, beta phi)
  | Bool _ | Var _ | Arith _ | Pred _ -> phi
