open Hflmc2_syntax
open Hflz
module PA = Infer_partial_application

let id_gen ?name ty =
  let id = Id.gen ?name ty in
  { id with name = id.name ^ string_of_int id.id }

(* TODO: optimize formula? *)
let make_guessed_terms (coe1 : int) (coe2 : int) vars =
  let mk_affine term coe1 coe2 = Arith.Op (Arith.Add, [Arith.Op (Mult, [Int coe1; term]); Int coe2]) in
  match vars |>
    List.map (fun var -> mk_affine (Var var) coe1 coe2 :: [mk_affine (Var var) (-coe1) coe2]) |>
    List.flatten with
  | [] -> [Arith.Int coe2]
  | vars -> vars

let formula_fold func terms = match terms with
    | [] -> failwith "[formula_fold] Number of elements should not be zero."
    | term::terms -> begin
      List.fold_left func term terms
    end

let make_approx_formula fa_var_f bounds = 
  bounds
  |> List.map (fun bound -> Pred (Lt, [Var fa_var_f; bound]))
  |> formula_fold (fun acc f -> Or (acc, f))

let rec to_ty = function
  | PA.TFunc (l, arg, body) -> begin
    match l with
    | PA.Insert ->
      Type.TyArrow (Id.gen Type.TyInt,
        Type.TyArrow (Id.gen (to_argty arg), to_ty body)
      )
    | PA.NoInsert ->
      Type.TyArrow (Id.gen (to_argty arg), to_ty body)
  end
  | TBool -> Type.TyBool ()
  | TInt -> assert false
  | TVar _ -> assert false
and to_argty = function
  | TInt -> Type.TyInt
  | t -> Type.TySigma (to_ty t)

let get_free_variables (phi : ('a, 'b) PA.thflz) =
  let rec go (phi : ('a, 'b) PA.thflz) =
    match phi with
    | Var v -> [v]
    | Arith a -> go_arith a
    | App (p1, p2) -> go p1 @ go p2
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (_, x, p1) -> List.filter (fun x' -> not @@ Id.eq x x') (go p1)
    | Pred (_, a) -> List.map go_arith a |> List.flatten
    | Bool _ -> []
    | Forall (x, p1) -> List.filter (fun x' -> not @@ Id.eq x x') (go p1)
    | Exists (x, p1) -> List.filter (fun x' -> not @@ Id.eq x x') (go p1)
  and go_arith a = match a with
    | Int _ -> []
    | Var x -> [x]
    | Op (_, a) -> List.map go_arith a |> List.flatten
  in
  go phi

let get_related_integer_variables
    global_vars
    (fvs : PA.insert_flag PA.ptype Id.t list)
    (env : (PA.insert_flag PA.ptype Id.t * PA.insert_flag PA.ptype Id.t list) list) =
  let integers, hos =
    List.partition
      (fun v ->
        match v.Id.ty with
        | PA.TInt -> true
        | _ -> false
      )
      fvs in
  let hos =
    hos 
    |> List.filter 
      (fun v ->
        not @@ List.exists (Id.eq v) global_vars
      )
    |> List.map
      (fun ho_v ->
        match List.find_all (fun (_, vs) -> List.exists (Id.eq ho_v) vs) env with
        | [(i, _)] -> i
        | [] -> print_endline ho_v.name; assert false
        | _ -> assert false
      )
    in
  integers @ hos
  |> List.map (fun v -> { v with Id.ty = `Int })
  |> Hflmc2_util.remove_duplicates Id.eq
  
let add_arguments_expr global_vars use_related (phi : PA.i_thflz) (coe1: int) (coe2: int) =
  (* env contains only integer variables *)
  let new_ids = ref IdMap.empty in
  let rec go_arith (a : PA.i_ptype PA.tarith) : Arith.t = match a with
    | Int i -> Int i
    | Var v -> Var {v with ty = `Int}
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in 
  let rec go_expr (env : (PA.insert_flag PA.ptype Id.t * PA.i_ptype Id.t list) list) (phi : PA.i_thflz) : unit Type.ty Hflz.t =
    match phi with
    | App _ -> begin
      (* Appのみを辿って、直近の祖先でAppでない部分式の直下に追加整数引数を追加する *)
      (* NOTE: 式の型がbool出ない場合はeta変換が必要 *)
      let ty = PA.get_thflz_type phi in
      assert (ty = TBool);
      (* (* スコープ内の整数引数の集合は同一なので、同一の整数変数を使う *)
      let id = id_gen Type.TyInt in
      let id_getter () = id in *)
      (* 高階引数ごとに別の整数変数を使う => こちらのほうがソルバで解きやすいようだ *)
      let id_getter () =
        id_gen ~name:"s" `Int in
      let phi, generated_ids = go_app env [] id_getter phi in
      (* let integers = List.map fst env in *)
      match generated_ids with
      | [] -> phi
      | generated_ids -> begin
        let scoped_integer_variables =
          env
          |> List.filter (fun (id, _) -> match id.Id.ty with PA.TInt -> true | _ -> false) 
          |> List.map (fun (id, _) -> { id with Id.ty = `Int }) in
        List.iter
          (fun (id, related_ids) ->
            let ids =
              if use_related then related_ids else scoped_integer_variables in
            new_ids := IdMap.add !new_ids ({id with Id.ty=Type.TyInt}) (Hflz_util.VTVarMax (List.map (fun id -> Arith.Var id) ids));
          )
          generated_ids;
        let bound =
          generated_ids |>
          List.map
            (fun (id, related_ids) ->
              let ids =
                if use_related then related_ids else scoped_integer_variables in
              let bound_terms = make_guessed_terms coe1 coe2 ids in
              let bound = make_approx_formula id bound_terms in
              bound
            ) |>
          formula_fold (fun a b -> Or (a, b)) in
        let body =
          Or (bound, phi) in
        let rec g xs b = match xs with
          | [] -> b
          | (x, _)::xs -> Forall ({x with ty=Type.TyInt}, g xs b) in
        g generated_ids body
      end
    end
    | Bool b -> Bool b
    | Var v -> Var {v with ty = to_ty v.ty }
    | Arith a -> Arith (go_arith a)
    | Pred (p, a) -> Pred (p, List.map go_arith a)
    | Or  (p1, p2) -> Or  (go_expr env p1, go_expr env p2)
    | And (p1, p2) -> And (go_expr env p1, go_expr env p2)
    | Abs (l, x, p) -> begin
      let env = Env.update [x, []] env in
      match l with
      | Insert ->
        let id = id_gen ~name:"t" Type.TyInt in
        new_ids := IdMap.add !new_ids id Hflz_util.VTHigherInfo;
        (* TODO: 関連する高階引数を追加 *)
        let rec get_abs acc phi = match phi with
          | PA.Abs (l, x, p) -> begin
            match l with
            | PA.NoInsert ->
              get_abs (x::acc) p
            | PA.Insert -> acc
          end
          | _ -> acc
        in
        let args = x::(get_abs [] p) in
        (* print_endline @@ "int=" ^ Id.to_string id ^ ", args=" ^ Hflmc2_util.show_list (fun id -> Id.to_string id) args; *)
        let env = Env.update [{id with ty=PA.TInt}, args] env in
        Abs (id, Abs ({x with ty=to_argty x.ty}, go_expr env p))
      | NoInsert ->
        Abs ({x with ty=to_argty x.ty}, go_expr env p)
    end
    | Forall (x, p) ->
      let env = Env.update [{x with ty=PA.TInt}, []] env in
      Forall ({x with ty=to_argty x.ty}, go_expr env p)
    | Exists (x, p) ->
      let env = Env.update [{x with ty=PA.TInt}, []] env in
      Exists ({x with ty=to_argty x.ty}, go_expr env p)
  and go_app env apps (id_getter : unit -> [`Int] Id.t) (phi : PA.i_thflz) : unit Type.ty Hflz.t * ([ `Int ] Id.t * [ `Int ] Id.t list) list =
    match phi with
    | App (p1, p2) -> begin
      let apps = p2::apps in
      let p2, generated_ids_in_arg =
        match p2 with
        | Arith a -> Arith (go_arith a), []
        | _ -> go_app env [] id_getter p2
      in
      let ty = PA.get_thflz_type p1 in
      match ty with
      | TFunc (l, _, _) -> begin
        match l with
        | PA.Insert ->
          let p1, generated_ids = go_app env [] id_getter p1 in
          let id = id_getter () in
          (* TODO: apps中の自由変数の情報を取得。高階変数と、それに関連する整数変数のmapを保持する必要がある。Absのときに生成して渡す？ *)
          (* print_endline "phi";
          print_endline (Hflmc2_util.fmt_string PA.pp_i_thflz phi); *)
          let fvs = List.map get_free_variables apps |> List.flatten |> Hflmc2_util.remove_duplicates Id.eq in
          let related_integer_variables = get_related_integer_variables global_vars fvs env in
          App (App (p1, Arith (Var id)), p2), ((id, related_integer_variables) :: generated_ids @ generated_ids_in_arg)
        | PA.NoInsert -> begin
          let p1, generated_ids = go_app env apps id_getter p1 in
          App (p1, p2), generated_ids @ generated_ids_in_arg
        end
      end
      | _ -> assert false
    end
    | _ -> go_expr env phi, []
  in
  let body = go_expr Env.empty phi in
  body, !new_ids

module Env_ = Env_no_value

let adjust_type_expr env phi =
  (* env contains only non-integer variables *)
  let rec go env phi = match phi with
    | Var x -> begin
      let x = 
        try
          Env_.lookup x env
        with Not_found ->failwith @@ "a variable not found in Env (maybe this variable cannot be determined to be an integer type): " ^ Id.to_string x in
      Var x
    end
    | Bool _ | Arith _ | Pred _ -> phi
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | And (p1, p2) -> And (go env p1, go env p2)
    | Abs (x, p) -> begin
      match x.ty with
      | TySigma ty ->
        Abs (x, go (Env_.update [{ x with ty = ty }] env) p)
      | TyInt ->
        Abs (x, go env p)
    end
    | Forall (x, p) ->
      Forall (x, go env p)
    | Exists (x, p) ->
      Exists (x, go env p)
    | App (p1, p2) -> App (go env p1, go env p2)    
  in
  go env phi

let adjust_type (hes : 'ty hes) =
  let entry, rules = hes in
  let env =
    Env_.create @@
    List.map
      (fun {var; _} -> var)
      rules in
  adjust_type_expr env entry,
  List.map
    (fun {var; fix; body} ->
      { var;
        fix;
        body = adjust_type_expr env body }
    )
    rules
  
let show_id_map id_map show_f = 
  "{" ^
  (IdMap.to_alist id_map
  |> List.map (fun (id, vt) -> "" ^ Id.to_string id ^ "=" ^ show_f vt)
  |> String.concat ", ") ^
  "}"

let add_arguments (hes : 'ty hes) (coe1: int) (coe2: int) (partial_analysis : bool) (use_related : bool) =
  let rules =
    if partial_analysis then
      Infer_partial_application.infer_partial_applications hes
    else
      Infer_partial_application.insert_all hes in
  let all_id_maps = ref [] in
  let rules =
    List.map
      (fun {PA.var; fix; body} ->
        let body, new_ids = add_arguments_expr (List.map (fun {PA.var; _} -> var) rules) use_related body coe1 coe2 in
        all_id_maps := new_ids :: !all_id_maps;
        let var = {var with ty=to_ty var.ty} in
        {var; fix; body}
      )
      rules in
  let hes = decompose_entry_rule rules in
  (* print_endline "result 1";
  print_endline @@ Hflz.show_hes Print.simple_ty hes;
  print_endline @@ Print_syntax.show_hes (merge_entry_rule hes); *)
  let hes = adjust_type hes in
  (* print_endline "result 2";
  print_endline @@ Hflz.show_hes Print.simple_ty hes;
  print_endline @@ Print_syntax.show_hes (merge_entry_rule hes); *)
  Hflz_typecheck.type_check hes;
  let all_id_map =
    List.fold_left (fun map acc ->
      (* should use merge_skewed *)
      IdMap.merge map acc ~f:(fun ~key:_ v ->
        match v with
        | `Left v -> Some v
        | `Right v -> Some v
        | `Both _ -> assert false
      )
    )
    IdMap.empty
    !all_id_maps in
  (* print_endline "id_map";
  print_endline @@ show_id_map all_id_map Hflz_util.show_variable_type; *)
  hes, all_id_map

let id_n n t = { Id.name = "x_" ^ string_of_int n; id = n; ty = t }

let to_ty_in_id id =
  match id.Id.ty with
  | Type.TySigma ty -> Hflz.Var {id with ty}
  | Type.TyInt -> Arith (Arith.Var {id with ty = `Int})

let to_int_in_id id =
  match id.Id.ty with
  | Type.TyInt -> Arith.Var {id with ty = `Int}
  | _ -> assert false
  
let%expect_test "add_arguments" =
  let open Type in
  (*   ∀x_11. (λx_22:int.λx_33:(int -> bool).x_33 x_22) 0 (λx_44:int.x_44 = x_11)   *)
  let v_n = id_n 1 TyInt in
  let v_x = id_n 2 TyInt in
  let v_f = id_n 3 (TySigma (TyArrow (id_n 0 TyInt, TyBool ()))) in
  let v_y = id_n 4 TyInt in
  let phi =
    Forall (v_n, App (App (Abs (v_x, Abs (v_f, App (to_ty_in_id v_f, to_ty_in_id v_x))), Arith (Int 0)), Abs (v_y, Pred (Eq, [to_int_in_id v_y; to_int_in_id v_n])))) in
  let hes = phi, [] in
  print_endline @@ Hflmc2_util.fmt_string (Print_syntax.hflz_hes Print.simple_ty_) hes;
  [%expect {|
    ∀x_11.
     (λx_22:int.λx_33:(int -> bool).x_33 x_22) 0 (λx_44:int.x_44 = x_11) |}];
  let ty' = Hflz_util.get_hflz_type phi in
  assert (ty' = Type.TyBool ());
  let hes, _ = add_arguments hes 10 20 true false in
  (* let phi = add_parameters_expr phi in *)
  ignore [%expect.output];
  print_endline @@ Hflmc2_util.fmt_string (Print_syntax.hflz_hes Print.simple_ty_) hes;
  [%expect {|
    ∀x_11.
     ∀s100100.
      s100100 < 10 * x_11 + 20 || s100100 < (-10) * x_11 + 20
      || (λx_22:int.λx_3_i101101:int.λx_33:(int -> bool).x_33 x_22) 0 s100100
          (λx_44:int.x_44 = x_11) |}];
  let phi, _ = hes in
  let ty' = Hflz_util.get_hflz_type phi in
  assert (ty' = Type.TyBool ());
