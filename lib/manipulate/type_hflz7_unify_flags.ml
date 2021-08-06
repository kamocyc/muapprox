open Hflmc2_syntax
open Type_hflz7_def

let unify_flags constraints =
  (* print_endline "flag_constraints (to solve):";
  print_endline @@ (Hflmc2_util.show_list show_use_flag_constraint constraints); *)
  List.iter
    (function
      | EF_Equal (a, b) ->
        assert (a <> dummy_use_flag);
        assert (b <> dummy_use_flag);
      | EF_Le (a, b) ->
        assert (a <> dummy_use_flag);
        assert (b <> dummy_use_flag);
    )
    constraints;
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
        | TUse, TUse -> None
        | TNotUse, TNotUse -> None
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
    | (TUse, TUse)::determined ->
      go_les_sub determined les
    | (TNotUse, TNotUse)::determined ->
      go_les_sub determined les
    | (_, _)::_ -> (* print_endline @@ Hflmc2_util.show_pairs show_use_flag show_use_flag determined; *) assert false
    | [] -> [], les
  in
  let rec go_les les =
    let determined, les =
      Hflmc2_util.partition_map
        ~f:(fun le ->
          match le with
          | (TUse, EFVar f2) -> `Fst (EFVar f2, TUse)
          | (EFVar f1, TNotUse) -> `Fst (EFVar f1, TNotUse)
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
        | (TUse, TUse)
        | (TNotUse, TNotUse)
        | (TNotUse, TUse) -> false
        | (TUse, TNotUse) -> failwith "a"
        | _ -> true
      )
      les in
  let subst_acc'' =
    List.map
      (fun le ->
        match le with
        | (EFVar id1, EFVar id2) ->
          [(id1, TNotUse); (id2, TNotUse)]
        | (EFVar id1, TUse) ->
          [(id1, TNotUse)]
        | (TNotUse, EFVar id2) ->
          [(id2, TNotUse)]
        | _ -> assert false
      )
      les
    |> List.concat
    |> Hflmc2_util.remove_duplicates (=) in
  let composed = compose_flags_substs (compose_flags_substs subst_acc' subst_acc'') subst_acc in
  (* print_endline "flag_constraints (subst_acc):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_use_flag subst_acc);
  print_endline "flag_constraints (subst_acc'):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_use_flag subst_acc');
  print_endline "flag_constraints (subst_acc''):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_use_flag subst_acc'');
  print_endline "flag_constraints (composed):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_use_flag composed);
  print_endline "flag_constraints (solved):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_use_flag composed); *)
  composed
