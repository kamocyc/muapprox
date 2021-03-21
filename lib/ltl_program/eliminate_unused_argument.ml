open Hflmc2_syntax
open Eliminate_unused_argument_util

let generate_constraints (hes : Type.simple_ty thes_rule list) =
  let pred_env = List.map (fun {var; body} -> (var, body)) hes in
  (* ensure all variables must have distinct ids *)
  let rec go (phi : Type.simple_ty thflz) = match phi with
    | Bool (id, _) -> M.init id [(TAVar id, TBool)]
    | Var (id, v) -> begin
      match List.find_opt (fun (var, _) -> Id.eq var v) pred_env with
      | None ->
         M.init id [(TAVar id, TBVar (Id.remove_ty v))]
      | Some (_, body) ->
        let pred_id = get_id body in
        M.init id [(TAVar id, TAVar pred_id)]
    end
    | Or (id, p1, p2) ->
      let m = M.merge (go p1) (go p2) in
      M.add m id [(TAVar id, TBool); (TAVar (get_id p1), TBool); (TAVar (get_id p2), TBool)]
    | And (id, p1, p2) ->
      let m = M.merge (go p1) (go p2) in
      M.add m id [(TAVar id, TBool); (TAVar (get_id p1), TBool); (TAVar (get_id p2), TBool)]
    | Abs (id, x, p1) ->
      let m = go p1 in
      M.add m id [(TAVar id, TFunc (TBVar (Id.remove_ty x), TAVar (get_id p1)))]
    | Forall (id, x, p1) ->
      let m = go p1 in
      M.add m id [(TAVar id, TAVar (get_id p1))]
    | Exists (id, x, p1) ->
      let m = go p1 in
      M.add m id [(TAVar id, TAVar (get_id p1))]
    | App (id, p1, p2) ->
      let m = M.merge (go p1) (go p2) in
      M.add m id [(TAVar (get_id p1), TFunc (TAVar (get_id p2), TAVar id))]
    | Arith (id, p1) ->
      let m = go_arith p1 in
      M.add m id [(TAVar id, TInt); (TAVar (get_id_arith p1), TInt)]
    | Pred (id, _, ps) ->
      let m = (List.map go_arith ps) |> M.merges in
      M.add m id ([(TAVar id, TBool)] @ (List.map (fun p -> (TAVar (get_id_arith p), TInt)) ps))
  and go_arith (phi : tarith) = match phi with
    | Int (id, _) -> M.init id [(TAVar id, TInt)]
    | Var (id, v) ->
      M.init id [(TAVar id, TInt); (TAVar id, TBVar (Id.remove_ty v))]
    | Op (id, _, ps) ->
      let m = (List.map go_arith ps) |> M.merges in
      M.add m id ([(TAVar id, TInt)] @ (List.map (fun p -> (TAVar (get_id_arith p), TInt)) ps))
  in
  let constraints =
    List.map (fun {var; body; fix} ->
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
      (fun xs -> List.map (fun (v1, v2) -> (subst_ctype v1 [pair], subst_ctype v2 [pair])) xs) in
  let merge_values m ~target:id1 ~source:id2 =
    let v1 = M.lookup m id1 in
    let v2 = M.lookup m id2 in
    let m = M.remove (M.remove m id2) id1 in
    M.add m id1 (v1 @ v2)
  in
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
  let rec unify (equals : (ctype * ctype) list) cond =
    (* save_to_file
      "unify.txt"
      (show_constraints cond ^ "\n" ^ Hflmc2_util.show_pairs show_ctype show_ctype equals);
    print_endline "unify";
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
  unified, M.to_list !remaining_cond |> List.map (fun (k, v) -> k), !synonyms
  
let replace_erasable_subtrees (rules : Type.simple_ty thes_rule list) elasables synonyms dummy_unit_var_name =
  let used = ref [] in (* for debug *)
  let rec go (phi : Type.simple_ty thflz) =
    let go_recur phi =
      match phi with
        | Bool _ | Var _ -> phi
        | Or (id, p1, p2) -> Or (id, go p1, go p2)
        | And (id, p1, p2) -> And (id, go p1, go p2)
        | Abs (id, x, p) -> Abs (id, x, go p)
        | Forall (id, x, p) -> Forall (id, x, go p)
        | Exists (id, x, p) -> Exists (id, x, go p)
        | App (id, p1, p2) -> App (id, go p1, go p2)
        | Arith (id, p) -> Arith (id, p)
        | Pred (id, e, ps) -> Pred (id, e, ps)
    in
    let id = get_id phi in
    match List.find_opt (fun v -> Id.eq v id) elasables with
    | Some v -> begin
      used := id :: !used;
      Var (id, { name = dummy_unit_var_name; id = -1; ty = Type.TyBool () } )
    end
    | None -> begin
      let m = IdMap.filter synonyms (fun ls -> List.exists (fun v' -> Id.eq v' id) ls) in
      if IdMap.length m > 0 then begin
        assert (IdMap.length m = 1);
        let (id', _) = IdMap.nth_exn m 0 in
        match List.find_opt (fun v -> Id.eq v id') elasables with
        | Some v -> begin
          used := id :: !used;
          Var (id, { name = dummy_unit_var_name; id = -1; ty = Type.TyBool () } )
        end
        | None -> go_recur phi
      end else
        go_recur phi
    end
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
  print_endline @@ Hflmc2_syntax.show_list Id.to_string !used;
  print_endline "remains";
  print_endline @@ Hflmc2_syntax.show_list Id.to_string remains; *)
  (* assert (List.length remains = 0); *)
  rules
  

let eliminate_unused_argument (hes : Type.simple_ty Hflz.hes) =
  let entry, rules = hes in
  let rules = (Hflz.mk_entry_rule entry) :: rules in
  let rules = assign_unique_variable_id rules in
  (* let () =
    let hes = abbrev_variable_names (Hflz.decompose_entry_rule rules) in
    ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"bb.txt" ~without_id:true true hes
    in *)
  let rules = assign_id_to_subterm rules in
  (* save_to_file "prog.txt" (show_s_thes_rules rules); *)
  (* print_endline @@ show_s_thes_rules rules; *)
  let constraints = generate_constraints rules in
  let unified, elasables, synonyms =
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
    ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"bb_elim.txt" ~without_id:true true hes
    in *)
  hes
