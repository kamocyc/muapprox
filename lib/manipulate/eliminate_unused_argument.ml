open Hflmc2_syntax
open Eliminate_unused_argument_util

(* elimination of unused arguments is based on "Type-Based Useless Variable Elimination, PEPM00" *)

let merge_values m ~target:id1 ~source:id2 =
  let v1 = M.lookup m id1 in
  let v2 = M.lookup m id2 in
  let m = M.remove (M.remove m id2) id1 in
  M.add m id1 (v1 @ v2)

let get_occurring_integer_variables (phi : Type.simple_ty thflz) =
  let remove v vars = List.filter (fun (_, v') -> not @@ Id.eq v v') vars in
  let rec go (phi : Type.simple_ty thflz) = match phi with
    | Bool _ -> []
    | Var _ -> []
    | Or (_, p1, p2)  -> go p1 @ go p2
    | And (_, p1, p2) -> go p1 @ go p2
    | Abs (_, x, p) -> remove x @@ go p
    | Forall (_, x, p) -> remove x @@ go p
    | Exists (_, x, p) -> remove x @@ go p
    | App (_, p1, p2) -> go p1 @ go p2
    | Arith (_, a) -> go_arith a
    | Pred (_, _, ls) -> List.map go_arith ls |> List.flatten
  and go_arith a = match a with
    | Int _ -> []
    | Var (id, v) -> [(id, v)]
    | Op (_, _, xs) -> List.map go_arith xs |> List.flatten
  in
  go phi

let update_id_map map id cond =
  IdMap.update map id ~f:(fun v  -> match v with
    | Some v -> cond @ v
    | None -> cond
  )

let merge_with_update_id_map m1 m2 =
  IdMap.merge m1 m2
    ~f:begin fun ~key:_key -> function
    | `Left x -> Some x
    | `Right x -> Some x
    | `Both (l, r) ->
      Some (l @ r)
    end

let generate_constraints id_type_map (hes : Type.simple_ty thes_rule list) =
  let merge_m m1 m2 =
    match M.merge_either m1 m2 with
    | Core.First m -> m
    | Core.Second (key, x1, x2) ->
      print_endline @@"key=" ^ Id.to_string key ^ ", left=" ^ Hflmc2_util.show_pairs show_ctype show_ctype x1 ^ ", right=" ^ Hflmc2_util.show_pairs show_ctype show_ctype x2;
      failwith "merge_m"
  in
  let pred_env = List.map (fun {var; body; _} -> (var, body)) hes in
  (* all variables must have distinct ids *)
  let rec go (phi : Type.simple_ty thflz) = match phi with
    | Bool (id, _) -> M.init id [(TAVar id, TBool)]
    | Var (id, v) -> begin
      match List.find_opt (fun (var, _) -> Id.eq var v) pred_env with
      | None ->
        (* local variable *)
         M.init id [(TAVar id, TBVar (Id.remove_ty v))]
      | Some (_, body) ->
        (* global *)
        let pred_id = get_id body in
        M.init id [(TAVar id, TAVar pred_id)]
    end
    | Or (id, p1, p2) ->
      let m = merge_m (go p1) (go p2) in
      M.add m id [(TAVar id, TBool); (TAVar (get_id p1), TBool); (TAVar (get_id p2), TBool)]
    | And (id, p1, p2) ->
      let m = merge_m (go p1) (go p2) in
      M.add m id [(TAVar id, TBool); (TAVar (get_id p1), TBool); (TAVar (get_id p2), TBool)]
    | Abs (id, x, p1) ->
      let m = go p1 in
      M.add m id [(TAVar id, TFunc (TBVar (Id.remove_ty x), TAVar (get_id p1)))]
    | Forall (id, _, p1) -> begin
      let rec get_max_vars acc phi = match phi with
        | Forall (id, x, p1) -> begin
          match IdMap.find id_type_map x with
          | Some var_category -> begin
            match var_category with
            | Hflz_util.VTVarMax _ ->
              get_max_vars ((id, x, (TAVar id, TAVar (get_id p1)))::acc) p1
            | _ -> assert false
          end
          | None -> phi, []
        end
        | Or _ -> phi, acc
        | _ -> phi, []
      in
      let body, vars = get_max_vars [] phi in
      match vars with
      | [] -> 
        let m = go p1 in
        M.add m id [(TAVar id, TAVar (get_id p1))]
      | vars -> begin
        match body with
        | Or (id_or, conditions, body) -> generate_max_var_constraints vars (id_or, conditions, body)
        | _ -> assert false
      end
    end
    | Exists (id, _, p1) ->
      let m = go p1 in
      M.add m id [(TAVar id, TAVar (get_id p1))]
    | App (id, p1, p2) ->
      let m = merge_m (go p1) (go p2) in
      M.add m id [(TAVar (get_id p1), TFunc (TAVar (get_id p2), TAVar id))]
    | Arith (id, p1) ->
      let m = go_arith p1 in
      M.add m id [(TAVar id, TInt); (TAVar (get_id_arith p1), TInt)]
    | Pred (id, _, [p1; p2]) ->
      let m = merge_m (go_arith p1) (go_arith p2) in
      M.add m id ([(TAVar id, TBool)] @ [(TAVar (get_id_arith p1), TInt); (TAVar (get_id_arith p2), TInt)])
    | Pred _ -> assert false
  and go_arith (phi : tarith) = match phi with
    | Int (id, _) -> M.init id [(TAVar id, TInt)]
    | Var (id, v) ->
      M.init id [(TAVar id, TInt); (TAVar id, TBVar (Id.remove_ty v))]
    | Op (id, _, [p1; p2]) ->
      let m = merge_m (go_arith p1) (go_arith p2) in
      M.add m id ([(TAVar id, TInt)] @ [(TAVar (get_id_arith p1), TInt); (TAVar (get_id_arith p2), TInt)])
    | Op _ -> assert false
  and generate_max_var_constraints vars (id_or, conditions, body)=
    let variables =
      get_occurring_integer_variables body
      |> List.filter (fun (_, v) -> List.exists (fun (_, v', _) -> Id.eq v' v) vars)
    in
    (* (phi_1 \/ phi_2) != unit  =>  phi_1 = bool && phi_2 = bool という制約は作らない *)
    let rec decompose_ors conditions = match conditions with
      | Or (_, p1, p2) -> merge_with_update_id_map (decompose_ors p1) (decompose_ors p2)
      | Pred (id_pred, Lt, [Var (_, x); _]) -> begin
        (* conditions is Pred *)
        let m = go conditions in
        let cond = (TAVar id_pred, TBool) in
        variables
        |> List.filter (fun (_, v) -> Id.eq v x)
        |> List.fold_left (fun m (usage_id, _) ->
          update_id_map m usage_id [cond]
        ) m
      end
      | _ -> assert false
    in
    
    let m = go body in
    (* constraints for forall *)
    let m = List.fold_left (fun m (id, _, constra) -> M.add m id [constra]) m vars in
    (* Orは、body側のみ =Bool という制約を入れる *)
    let m = M.add m id_or [(TAVar id_or, TBool); (TAVar (get_id body), TBool)] in
    let m =
      merge_with_update_id_map
        m
        (decompose_ors conditions) in
    m
  in
  let constraints =
    List.map (fun {body; _} ->
      let m = go body in
      m
    ) hes
    |> M.merges in
  constraints

let solve equals cond =
  let is_equal_ctype = (=) in
  let subst_equals xs pair = List.map (fun (p1, p2) -> (subst_ctype p1 [pair], subst_ctype p2 [pair])) xs in
  let subst_equalities cond pair =
    M.map
      cond
      ~f:(fun xs -> List.map (fun (v1, v2) -> (subst_ctype v1 [pair], subst_ctype v2 [pair])) xs) in
  let get_new_equalities id cond =
    match M.find cond id with
    | Some t ->
      t, (M.remove cond id)
    | None -> assert false
  in
  let remaining_cond = ref (M.empty) in
  let synonyms = ref (M.empty) in
  let add_synonyms ~target ~source =
    (* print_endline @@ "add_synonyms!!! (target=" ^ string_of_int target.Id.id ^ ", source=" ^ string_of_int source.Id.id ^ ")"; *)
    (* sourceをマージ元とし、targetに追加 *)
    let sval =
      match M.find !synonyms source with
      | None -> []
      | Some a ->
        synonyms := M.remove !synonyms source;
        a in
    let tval =
      match M.find !synonyms target with
      | None -> []
      | Some a ->
        synonyms := M.remove !synonyms target;
        a in
    synonyms := M.add !synonyms target (source :: tval @ sval)
  in
  (* let count = ref 10000 in *)
  let rec unify (equals : (ctype * ctype) list) cond =
    (* save_to_file
      ("unify" ^ string_of_int !count ^ ".txt")
      (show_constraints cond ^ "\n" ^ Hflmc2_util.show_pairs show_ctype show_ctype equals);
    count := !count + 1; *)
    (* print_endline "unify";
    print_endline @@ show_constraints cond;
    print_endline @@ Hflmc2_util.show_pairs show_ctype show_ctype equals; *)
    match equals with
    | [] -> begin
      remaining_cond := cond;
      []
    end
    | (ty1, ty2)::xs -> begin
      if is_equal_ctype ty1 ty2 then
        unify xs cond
      else begin
        match ty1, ty2 with
        | TFunc (ty11, ty12), TFunc (ty21, ty22) ->
          unify ((ty11, ty21)::(ty12, ty22)::xs) cond
        | TAVar id1, TAVar id2 ->
          (* a_1 = a_2  の場合、a_1にa_2を代入 *)
          let xs = subst_equals xs (TAVar id1, TAVar id2) in
          let m = subst_equalities cond (TAVar id1, TAVar id2) in
          let m = merge_values m ~target:id2 ~source:id1 in
          add_synonyms ~target:id2 ~source:id1;
          unify xs m
        | TBVar _, ty2 ->
          let unified = unify (subst_equals xs (ty1, ty2)) (subst_equalities cond (ty1, ty2)) in
          compose_subst (ty1, ty2) unified
        | ty1, TBVar _ -> unify ((ty2, ty1)::xs) cond
        | TAVar id1, ty2 ->
          (* TODO: occur check => 既に型が付いている前提なので不要？ *)
          let new_equals, cond' = get_new_equalities id1 cond in
          let unified = unify (subst_equals (xs @ new_equals) (ty1, ty2)) (subst_equalities cond' (ty1, ty2)) in
          compose_subst (ty1, ty2) unified
        | ty1, TAVar id2 ->
          unify ((TAVar id2, ty1)::xs) cond
        | _ -> failwith @@ "unify: ty1=" ^ show_ctype ty1 ^ ", ty2=" ^ show_ctype ty2
      end
    end
  in
  let unified = unify equals cond in
  unified, M.to_list !remaining_cond |> List.map (fun (k, _) -> k), !synonyms

(* replace erasable (which can be unit-type) sub-expressions with variables named as dummy_unit_var_name, which are removed by infer_and_eliminate_unit_type_terms function *)
let replace_erasable_subtrees (rules : Type.simple_ty thes_rule list) elasables synonyms dummy_unit_var_name =
  let used = ref [] in (* for debug *)
  let rec go (phi : Type.simple_ty thflz) =
    let id = get_id phi in
    match List.find_opt (fun v -> Id.eq v id) elasables with
    | Some _ -> begin
      used := id :: !used;
      Var (id, { name = dummy_unit_var_name; id = -1; ty = Type.TyBool () } )
    end
    | None -> begin
      let m = IdMap.filter synonyms ~f:(fun ls -> List.exists (fun v' -> Id.eq v' id) ls) in
      if IdMap.length m > 0 then begin
        assert (IdMap.length m = 1);
        let (id', _) = IdMap.nth_exn m 0 in
        match List.find_opt (fun v -> Id.eq v id') elasables with
        | Some _ -> begin
          used := id :: !used;
          Var (id, { name = dummy_unit_var_name; id = -1; ty = Type.TyBool () } )
        end
        | None -> go_recur phi
      end else
        go_recur phi
    end
  and go_recur phi =
    match phi with
      | Bool _ | Var _ -> phi
      | Or (id, p1, p2) -> begin
        let is_dummy v = match v with
          | Var (_, { name; id; ty } ) when name = dummy_unit_var_name && id = id && ty = Type.TyBool () -> true
          | _ -> false
        in
        let p1 = go p1 in
        let p2 = go p2 in
        if is_dummy p1 && is_dummy p2
        then
          Var (id, { name = dummy_unit_var_name; id = -1; ty = Type.TyBool () } )
        else if is_dummy p1 then
          p2
        else if is_dummy p2 then
          p1
        else Or (id, p1, p2)
      end
      | And (id, p1, p2) -> And (id, go p1, go p2)
      | Abs (id, x, p) -> Abs (id, x, go p)
      | Forall (id, x, p) -> Forall (id, x, go p)
      | Exists (id, x, p) -> Exists (id, x, go p)
      | App (id, p1, p2) -> App (id, go p1, go p2)
      | Arith (id, p) -> Arith (id, p)
      | Pred (id, e, ps) -> Pred (id, e, ps)
  in
  let rules =
    List.map (fun {var; body; fix} ->
      let body = go body in
      {var; body; fix}
    )
    rules in
  (* print_endline @@ show_s_thes_rules rules; *)
  (* let remains = List.filter (fun e -> not @@ List.exists (fun u -> Id.eq u e) !used ) elasables in
  print_endline "used";
  print_endline @@ Hflmc2_util.show_list Id.to_string !used;
  print_endline "remains";
  print_endline @@ Hflmc2_util.show_list Id.to_string remains; *)
  (* assert (List.length remains = 0); *)
  rules
  

let eliminate_unused_argument ?(id_type_map = IdMap.empty) (hes : Type.simple_ty Hflz.hes) =
  let rules = Hflz.merge_entry_rule hes in
  let rules, id_change_map = Hflz_util.assign_unique_variable_id rules in
  let id_type_map = Hflz_util.update_id_type_map id_type_map id_change_map in
  (* let () =
    let hes = abbrev_variable_names (Hflz.decompose_entry_rule rules) in
    ignore @@ Print_syntax.MachineReadable.save_hes_to_file ~file:"bb.txt" ~without_id:true true hes
    in *)
  let rules = assign_id_to_subterm rules in
  (* save_to_file "prog.txt" (show_s_thes_rules rules);
  print_endline @@ show_s_thes_rules rules; *)
  let constraints = generate_constraints id_type_map rules in
  let _unified, elasables, synonyms =
    let first_id = get_id (List.nth rules 0).body in
    solve [(TAVar (first_id), TBool)] constraints in
  let rules = replace_erasable_subtrees rules elasables synonyms Type_hflz.dummy_unit_var_name in
  (* print_endline "replace_erasable_subtrees";
  Print_temp.print_hes rules;
  print_endline @@ show_s_thes_rules rules;
  print_endline @@ show_constraints constraints;
  print_endline @@ Hflmc2_util.show_pairs show_ctype show_ctype unified; *)
  let rules = remove_id_form_subterm rules in
  let hes = Type_hflz.infer_and_eliminate_unit_type_terms (Hflz.decompose_entry_rule rules) in
  (* let () =
    let hes = abbrev_variable_names hes in
    ignore @@ Print_syntax.MachineReadable.save_hes_to_file ~file:"bb_elim.txt" ~without_id:true true hes
    in *)
  hes
