open Hflmc2_syntax.Hflz

let get_dependency_graph (hes : 'a hes_rule list) =
  let preds = List.mapi (fun i {var; _} -> (i, var)) hes in
  let graph_size = List.length hes in
  let graph = Mygraph.init graph_size in
  (* 参照の依存グラフを作成 *)
  List.iteri
    (fun index {var; body; _} -> 
      fvs body
      |> Hflmc2_syntax.IdSet.to_list
      |> List.filter_map
        (fun v ->
          List.find_opt (fun (_, v') -> Hflmc2_syntax.Id.eq v' v) preds
        )
      |> List.iter (fun (i', v') -> 
        Mygraph.add_edge index i' graph
      )
    )
    hes;
  preds, graph

let show_hflz hflz = show Hflmc2_syntax.Type.pp_simple_ty hflz

let get_hflz_type phi =
  let open Hflmc2_syntax.Type in
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
    | Forall (x, f1) -> go f1
    | Exists (x, f1) -> go f1
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
    | Pred (p, args) -> TyBool ()
    | Arith t -> failwith "Illegal type (Arith)"
  in
  go phi
