module Print = Print_syntax
module Fixpoint = Hflmc2_syntax.Fixpoint
module Formula = Hflmc2_syntax.Formula
module IdSet = Hflmc2_syntax.IdSet

open Hflz_typecheck
open Hflz
(* module Util = Hflmc2_util *)

let simplify_bound = ref false

let show_hflz = Print.show_hflz
let show_hflz_full = Print.show_hflz_full

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

(* Arrow type to list of types of the arguments conversion *)
(* t1 -> t2 -> t3  ==> [t3; t2; t1]  *)
let to_args : Type.simple_ty -> Type.simple_ty Type.arg Id.t list =
  let rec go =
    fun acc ty -> match ty with
    | Type.TyArrow (arg, ty) -> go (arg::acc) ty
    | Type.TyBool _ -> acc in
  go []

(* 引数のリストからabstractionに変換。IDは新規に生成する。 *)
let to_abs : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) = fun args ->
  let name_map = List.map (fun arg -> (arg.Id.name, Id.gen ~name:arg.Id.name arg.Id.ty)) args in
  fun body -> 
    let rec go = function
      | [] -> body
      | arg::xs -> Abs (List.assoc arg.Id.name name_map, go xs) in
    go args

(* Absの引数のIDを新規に生成しない版 *)
(* [x1; x2] body  ->  \x1. \x2. body *)
let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args

let to_forall args body =
  let rec go = function
    | [] -> body
    | arg::xs -> Forall(arg, go xs) in
  go args
  
(* Abstractionから、それに適用する変数の列を生成 *)
let to_vars : 'ty Hflz.t -> ('ty Hflz.t -> 'ty Hflz.t) = fun hfl ->
  fun body ->
    let rec go: 'ty Hflz.t -> 'ty Hflz.t = function
      | Abs ({id;ty;name}, child) -> begin
        match ty with
        | Type.TyInt -> 
          App (go child, Arith (Var {name; id; ty=`Int}))
        | Type.TySigma x -> 
          App (go child, Var {name; id; ty=x})
      end
      | _ -> body in
    go hfl

let to_app inner terms =
  let rec go terms = match terms with
    | t::ts -> App (go ts, t)
    | [] -> inner in
  go @@ List.rev terms

let argty_to_ty {Id.name; id; ty} =
  match ty with
  | Type.TyInt -> 
    Arith (Var {name; id; ty=`Int})
  | Type.TySigma x -> 
    Var {name; id; ty=x}

let make_guessed_terms (coe1 : int) (coe2 : int) vars =
  let mk_affine term coe1 coe2 = Arith.Op (Arith.Add, [Arith.Op (Mult, [Int coe1; term]); Int coe2]) in
  match vars |>
    List.map (fun var -> mk_affine (Var var) coe1 coe2 :: [mk_affine (Var var) (-coe1) coe2]) |>
    List.flatten with
  | [] -> [Arith.Int coe2]
  | vars -> vars

let make_guessed_terms_simple (coe1 : int) (coe2 : int) vars =
  let open Arith in
  (Int coe2)::(
    (List.map (fun v -> Op (Mult, [Int coe1; Var v])) vars)@
    (List.map (fun v -> Op (Mult, [Int (-coe1); Var v])) vars))
  
let formula_fold func terms = match terms with
    | [] -> failwith "[formula_fold] Number of elements should not be zero."
    | term::terms -> begin
      List.fold_left func term terms
    end

let make_approx_formula fa_var_f bounds = 
  bounds
  |> List.map (fun bound -> Pred (Lt, [Var fa_var_f; bound]))
  |> formula_fold (fun acc f -> Or (acc, f))

let filter_int_variable =
  List.filter_map
    (fun ({Id.ty; _} as var) ->
      match ty with
      | Type.TyInt -> Some ({var with ty=`Int})
      | Type.TySigma _ -> None 
    )

(* abstractioの順序を逆にする *)
let rev_abs hflz =
  let rec get_abs acc hflz =
    match hflz with
    | Abs (x, hflz) ->
      get_abs (x::acc) hflz
    | _ -> (hflz, acc) in
  let (body, vars) = get_abs [] hflz in
  to_abs' vars body

let extract_head_abstracts : Type.simple_ty Hflz.t -> ((Type.simple_ty Hflz.t -> Type.simple_ty Hflz.t) * Type.simple_ty Hflz.t) = fun hfl -> 
  ((fun body ->     
    let rec rep2 = fun hfl -> match hfl with
    | Abs (arg, child) -> Abs(arg, rep2 child)
    | _ -> body in
    rep2 hfl),
  let rec rep1 = fun hfl -> match hfl with
    | Abs (_, child) -> rep1 child
    | _ -> hfl in
    rep1 hfl)

(* base [x1; x2]  ->  (x1 -> x2 -> base) *)
let to_arrow_type ?base:(base=Type.TyBool ()) args  =
  let rec go acc args = match args with
    | arg::xs -> begin
      go (Type.TyArrow (arg, acc)) xs
    end
    | [] -> acc in
  go base (List.rev args)

let arg_id_to_var (x : 'ty Type.arg Id.t) = 
  match x.Id.ty with
  | Type.TySigma t -> Var {x with ty=t}
  | Type.TyInt -> Arith (Var {x with ty=`Int})

 (* : Type.simple_ty Type.arg Id.t list -> Type.simple_ty *)
let args_ids_to_apps (ids : 'ty Type.arg Id.t list) : ('ty Hflz.t -> 'ty Hflz.t) = fun body ->
  let rec go ids = match ids with
    | x::xs -> App (go xs, arg_id_to_var x)
    | [] -> body in
  go @@ List.rev ids

let args_hfl_to_apps (phis : 'ty Hflz.t list) : ('ty Hflz.t -> 'ty Hflz.t) = fun body ->
  let rec go phis = match phis with
    | x::xs -> App (go xs, x)
    | [] -> body in
  go @@ List.rev phis
  
let extract_abstraction phi not_apply_vars new_rule_name_base =
  let xs, phi' = decompose_abs phi in
  (* print_endline "extract_abstraction";
  List.iter (fun x -> print_endline @@ Id.to_string x) xs; *)
  (* 型情報も入っている。 *)
  (* arithの中のfvも見ている *)
  let free_vars =
    Hflz.fvs_with_type phi
    |> Id.remove_vars not_apply_vars in
  (* show *)
  (* print_endline "not_apply";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") not_apply_vars;
  print_endline "freevars";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") free_vars; *)
  (* TODO: 順番正しい？ *)
  let arr_type = to_arrow_type (free_vars @ xs) in
  let new_rule_id = Id.gen ~name:(new_rule_name_base ^ "_sub" ^ string_of_int (Id.gen_id ())) arr_type in
  let new_rule = {
    var = new_rule_id;
    body = (to_abs' (free_vars @ xs) phi');
    fix = Fixpoint.Greatest } in
  (* print_endline "NEW_RULE";  
  print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_ ) new_rule; *)
  let new_sub_formula = args_ids_to_apps free_vars @@ Var new_rule_id in
  (new_sub_formula, new_rule)

(* (∀x1. ∀x2. \y1. \y2. phi)  ->  (\y1. \y2. ∀x1. ∀x2. phi) *)
let in_forall v =
  let rec forall_vars phi acc = match phi with
    | Forall (x, phi') -> forall_vars phi' (x::acc)
    | _ -> acc, phi in
  let rec abs_vars phi acc = match phi with
    | Abs (x, phi') -> abs_vars phi' (x::acc)
    | _ -> acc, phi in
  let fvars, v = forall_vars v [] in
  let avars, v = abs_vars v [] in
  to_abs' (List.rev avars) (to_forall (List.rev fvars) v)  

      
type forall_or_exists =
  | FE_Forall of Type.simple_ty Type.arg Id.t
  | FE_Exists of Type.simple_ty Type.arg Id.t

(* phiの中のlambdaをdecomposeする *)
let decompose_lambda_ (phi : Type.simple_ty Hflz.t) (rule_id : Type.simple_ty Id.t) (hes_var_names : unit Id.t list) =
  let new_rules = ref [] in
  let mk_quant quants body =
    let rec go quants =
      match quants with
      | q::qs -> begin
        match q with
        | FE_Forall x -> Forall (x, go qs)
        | FE_Exists x -> Exists (x, go qs)
      end
      | [] -> body in
    go @@ List.rev quants in
  let rec go quant_acc phi = match phi with
    | Var _ | Bool _ | Arith _ |  Pred _ -> mk_quant quant_acc phi
    | Or (phi1,phi2) -> mk_quant quant_acc @@ Or(go [] phi1, go [] phi2)
    | And(phi1,phi2) -> mk_quant quant_acc @@ And(go [] phi1, go [] phi2)
    | App(phi1,phi2) -> mk_quant quant_acc @@ App(go [] phi1, go [] phi2)
    | Abs(_, _)    -> begin
      (* let v, new_rule = extract_abstraction phi ((Id.remove_ty rule_id)::hes_var_names) rule_id.name in
      new_rules := new_rule :: !new_rules;
      (* Log.app begin fun m -> m ~header:("Abs") "%a"
        Print.(hflz simple_ty_) v
      end; *)
      v *)
      let not_apply_vars =
        (List.map
          (fun q -> (match q with FE_Exists e -> e | FE_Forall e -> e) |> Id.remove_ty)
          quant_acc
        ) @
        (Id.remove_ty rule_id :: hes_var_names) in
      let v, new_rule = extract_abstraction phi not_apply_vars rule_id.name in
        (* Log.app begin fun m -> m ~header:("Forall 前" ^ x.name) "%a"
          Print.(hflz simple_ty_) new_rule.body
        end; *)
        let new_rule = { new_rule with body = in_forall @@ mk_quant quant_acc new_rule.body } in
        (* Log.app begin fun m -> m ~header:("Forall 後" ^ x.name) "%a"
          Print.(hflz simple_ty_) new_rule.body
        end; *)
        new_rules := new_rule :: !new_rules;
        v
    end
    | Forall (x, phi) -> go ((FE_Forall x)::quant_acc) phi
    | Exists (x, phi) -> go ((FE_Exists x)::quant_acc) phi
  in
  (* 先頭のAbstractionは読み飛ばす *)
  let rec go' phi = match phi with
    | Abs(x, phi) -> begin
      Abs(x, go' phi)
    end
    | _ -> go [] phi
  in
  (* Log.app begin fun m -> m ~header:"original formula" "%a"
    Print.(hflz simple_ty_) phi
  end; *)
  let res = go' phi in
  (* Log.app begin fun m -> m ~header:"converted formula" "%a"
    Print.(hflz simple_ty_) res
  end;
  Log.app begin fun m -> m ~header:"added_rules" "%a"
    Print.(hflz_hes simple_ty_) !new_rules
  end; *)
  (!new_rules, res)

(* abstractionをHESのequationに切り出す。 *)
(* これは、単一のruleに関するものである。 *)
let decompose_lambdas hes_names (rule : Type.simple_ty hes_rule) = 
  let rec go ({body; var; _} as rule) = 
    let new_rules, res = decompose_lambda_ body var hes_names in
    match new_rules with
    | [] -> [{rule with body = res}]
    | xs -> begin
      let xs = List.map (fun r -> go r) xs in
      {rule with body = res} :: List.flatten xs
    end in
  go rule

let decompose_lambdas_hes (entry, rules) =
  let hes_names = List.map (fun {var; _} -> Id.remove_ty var) rules in
  let rules = (mk_entry_rule entry) :: rules in
  let rules = rules |> List.map (decompose_lambdas hes_names) |> List.flatten in
  Hflz.decompose_entry_rule rules
  
let get_top_rule hes =
  match hes with
  | []  -> failwith "empty"
  | [x] -> x, []
  | x::xs -> begin
    match x with
    | { var=({ty=Type.TyBool ();_} as var); body; fix=Fixpoint.Greatest } -> begin
      let fvs = Hflz.fvs_with_type body in
      match List.find_opt (fun fv -> Id.eq fv var) fvs with
      | None -> x, xs
      | Some _ -> failwith "(get_top_rule 1) not implemented"
    end
    | _ -> failwith "(get_top_rule 2) not implemented"
  end

let get_dual_hes ((entry, rules) : Type.simple_ty hes): Type.simple_ty hes =
  let entry = Hflz.negate_formula entry in
  let results = List.map (fun rule -> Hflz.negate_rule rule) rules in
  let hes = (entry, results) in
  Log.app begin fun m -> m ~header:"get_dual_hes" "%a" Print.(hflz_hes simple_ty_) hes end;
  type_check hes;
  entry, results

let subst_arith_var replaced formula =
  let rec go_arith arith = match arith with
    | Arith.Int _ -> arith
    | Arith.Op (x, xs) -> Arith.Op(x, List.map go_arith xs)
    | Arith.Var x -> replaced x in
  let rec go_formula formula = match formula with
    | Bool _ | Var _ -> formula
    | Or (f1, f2) -> Or(go_formula f1, go_formula f2)
    | And (f1, f2) -> And(go_formula f1, go_formula f2)
    | Abs (x, f1) -> Abs(x, go_formula f1)
    | Forall (x, f1) -> Forall(x, go_formula f1)
    | Exists (x, f1) -> Exists(x, go_formula f1)
    | App (f1, f2) -> App(go_formula f1, go_formula f2)
    | Arith t -> Arith (go_arith t)
    | Pred (x, f1) -> Pred (x, List.map go_arith f1) in
  go_formula formula
  
let var_as_arith v = {v with Id.ty=`Int}

let rec to_tree seq f b = match seq with
  | [] -> b
  | x::xs -> f x (to_tree xs f b)


  
let encode_body_exists_formula_sub new_pred_name_cand coe1 coe2 hes_preds hfl = 
  let open Type in
  let formula_type_vars = Hflz_util.get_hflz_type hfl |> to_args |> List.rev in
  (* get free variables *)
  let free_vars =
    Hflz.fvs_with_type hfl
    |> Id.remove_vars hes_preds in
  let bound_vars, hfl =
      (* sequence of existentially bound variables *)
    let rec go acc hfl = match hfl with
      | Exists (x, hfl) -> go (x::acc) hfl
      | _ -> (acc, hfl) in
    let (bound_vars, hfl) = go [] hfl in
    (* ensure all variables are integer type (or not used) *)
    bound_vars |>
    List.rev |>
    List.filter_map (fun var -> 
      match var.Id.ty with
      | TyInt ->
        Some var
      | TySigma _ -> begin
        if (Hflz.fvs_with_type hfl
          |> List.exists (fun fv -> Id.eq fv var))
          then failwith "encode_body_exists_formula_sub: higher-order bound variable is not supported";
        (* when variable is not used *)
        None
      end
    ), hfl in
  let arg_vars = free_vars @ formula_type_vars @ bound_vars  in
  let new_pvar =
    let i = Id.gen_id() in
    let name =
      match new_pred_name_cand with
      | None -> "Exists" ^ string_of_int i
      | Some p -> p ^ "_e" ^ string_of_int i in
    let ty =
      (* TODO: higher-order vars *)
      to_tree
        arg_vars
        (fun x rem -> TyArrow (x, rem))
        (TyBool ())  in
    { Id.name = name; ty = ty; id = i } in
  let body =
    let guessed_terms = make_guessed_terms_simple coe1 coe2 (free_vars |> filter_int_variable) in
    let approx_formulas =
      bound_vars
      |> List.rev
      |> List.map (fun bound_var ->
        make_approx_formula
          {bound_var with ty=`Int}
          guessed_terms
      ) in
    rev_abs (
      (formula_type_vars |> List.rev |> to_abs') @@
        to_tree
        (bound_vars)
        (fun x rem -> Forall (x, rem)) @@
          Or (
            formula_fold (fun acc f -> Or(acc, f)) approx_formulas,
            args_ids_to_apps arg_vars @@ (Var new_pvar)
            )) in
    body,
    [{ 
      Hflz.var = new_pvar;
      fix = Fixpoint.Greatest;
      body =
        (arg_vars |> to_abs') @@
        And (
          ((* substitute rec vars to negative *)
          (* NOTE: exponential grow-up *)
          let rec go acc vars = match vars with
            | [] -> acc
            | x::xs ->
              go (acc |>
                  List.map (fun hfl -> 
                    hfl::[
                      subst_arith_var
                        (fun vid -> if Id.eq vid x then (Arith.Op (Sub, [Int 0; Var {x with ty=`Int}])) else Var vid) hfl]) |>
                  List.flatten)
                  xs in
          let terms1 =
            (go [hfl] bound_vars)
            |> List.map (fun f -> args_ids_to_apps formula_type_vars f) in
          let terms2 = 
            bound_vars |>
            List.map (fun var ->
              arg_vars
              |> List.map (fun v -> if Id.eq v var then Arith (Op (Sub, [Var {v with ty=`Int}; Int 1])) else arg_id_to_var v)
              |> List.fold_left
                (fun acc t -> App (acc, t))
                (Var new_pvar)
              ) in
          (terms1 @ terms2) |> formula_fold (fun acc f -> Or (acc, f))),
          bound_vars
          |> List.map (fun var -> Pred (Ge, [Var {var with ty=`Int}; Int 0]))
          |> formula_fold (fun acc f -> And (acc, f))
        )
    }]

let encode_body_exists_formula new_pred_name_cand coe1 coe2 hes_preds hfl =
  let new_rules = ref [] in
  let rec go hes_preds hfl = match hfl with
    | Var _ | Bool _ -> hfl
    | Or (f1, f2)  -> Or  (go hes_preds f1, go hes_preds f2)
    | And (f1, f2) -> And (go hes_preds f1, go hes_preds f2)
    | Abs (v, f1)  -> Abs (v, go hes_preds f1)
    | Forall (v, f1) -> Forall (v, go hes_preds f1)
    | Exists (v, f1) -> begin
      if v.ty <> Type.TyInt then (
        (* boundされている変数の型が整数以外 *)
        match IdSet.find (fvs f1) ~f:(fun i -> Id.eq i v) with
        | None ->
          (* boundされている変数が使用されない、つまり無駄なboundなので無視 *)
          go hes_preds f1
        | Some x -> failwith @@ "quantifiers for higher-order variables are not implemented (" ^ x.name ^ ")"
      ) else (
        let hfl, rules = encode_body_exists_formula_sub new_pred_name_cand coe1 coe2 hes_preds hfl in
        let new_rule_vars = List.map (fun rule -> { rule.var with ty = Type.TySigma rule.var.ty }) rules in
        let rules = List.map (fun rule -> { rule with body = go (new_rule_vars @ hes_preds) rule.body } ) rules in
        new_rules := rules @ !new_rules;
        hfl
      )
    end
    | App (f1, f2) -> App (go hes_preds f1, go hes_preds f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t) in
  let hfl = go hes_preds hfl in
  hfl, !new_rules

(* hesからexistentialを除去 *)
let encode_body_exists coe1 coe2 (hes : Type.simple_ty Hflz.hes) =
  let (entry, rules) = hes in
  let env = List.map (fun {var; _} -> { var with ty=Type.TySigma var.ty }) rules in
  let entry, new_rules = encode_body_exists_formula None coe1 coe2 env entry in
  let rules =
    rules |>
    List.map
      (fun {var; fix; body} -> 
        let body, new_rules = encode_body_exists_formula (Some var.name) coe1 coe2 env body in
        {var; fix; body}::new_rules
      )
    |> List.flatten in
  (entry, new_rules @ rules)

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
        beta @@ Hflmc2_syntax.Trans.Subst.Hflz.hflz (Hflmc2_syntax.IdMap.of_list [x, phi2]) phi1
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
  

(* let%expect_test "beta" =
  App () *)

let get_outer_mu_funcs (funcs : 'a hes_rule list) =
  let funcs_count = List.length funcs in
  (* construct a table *)
  let pvar_to_nid = Hashtbl.create funcs_count in
  let nid_to_pvar, is_mu =
    funcs
    |> List.mapi
      (fun nid {fix; var; _} ->
        Hashtbl.add pvar_to_nid var nid;
        (var, fix = Fixpoint.Least)
      )
    |> List.split in
  (* make a graph *)
  let _, g = Hflz_util.get_dependency_graph funcs in
  (* make a rev graph *)
  let rg = Mygraph.reverse_edges g in
  (* get nid list s.t. a ->* b /\ b *<- a through only min(a, b) nodes *)
  let outer_nids = Mygraph.init funcs_count in
  for i = 0 to funcs_count - 1 do
    let nids1 = Mygraph.reachable_nodes_from ~start_is_reachable_initially:false i g in
    let nids2 = Mygraph.reachable_nodes_from ~start_is_reachable_initially:false i rg in
    Core.Set.Poly.inter
      (Core.Set.Poly.of_list nids1)
      (Core.Set.Poly.of_list nids2)
    |> Core.Set.Poly.to_list
    |> List.iter
      (fun nid ->
         Mygraph.add_edge nid i outer_nids
      );
    Mygraph.reset_node i g;
    Mygraph.reset_node i rg
  done;
  (* filter by fixpoints *)
  let res =
    List.map
      (fun {var=pvar; _} ->
         let nid = Hashtbl.find pvar_to_nid pvar in
         pvar,
         Mygraph.get_next_nids nid outer_nids
         |> List.filter
           (fun to_nid -> List.nth is_mu to_nid)
         |> List.map
           (fun to_nid ->
              List.nth nid_to_pvar to_nid
           )
      )
      funcs
  in
  (* print_endline "get_outer_mu_funcs";
  List.map (fun (pvar, pvars) -> Printf.sprintf "%s: %s" (pvar.Id.name) (List.map (fun v -> v.Id.name) pvars |> String.concat ", ")) res
     |> String.concat "\n"
     |> print_endline; *)
  Env.create res

let rectvar_prefix = "rec"
let rectvar_of_pvar pvar =
  let id = Id.gen_id () in
  { 
    Id.name = rectvar_prefix ^ pvar.Id.name ^ string_of_int id;
    id = id;
    ty = Type.TyInt;
  }

(* TODO: 元からrecがprefixの場合 *)
let is_rectvar v =
  String.length v.Id.name >=3 &&
  String.sub v.Id.name 0 3 = rectvar_prefix

let get_occuring_arith_terms phi = 
  (* remove expressions that contain locally bound variables *)
  let remove ls x =
    List.filter (fun (expr, vars) -> not @@ List.exists ((=) (Id.remove_ty x)) vars) ls
  in
  let rec go_hflz phi = match phi with
    | Bool _ -> []
    | Var v -> [] (* use only arithmetic variable *)
    | Or (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | And (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Abs (x, p1) -> remove (go_hflz p1) x
    | Forall (x, p1) -> remove (go_hflz p1) x
    | Exists (x, p1) -> remove (go_hflz p1) x
    | App (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Arith (a) -> [(a, get_occurring_arith_vars a)]
    | Pred (p, xs) -> List.map (fun a -> (a, get_occurring_arith_vars a)) xs
  and get_occurring_arith_vars phi = match phi with
    | Int _ -> []
    | Var v -> [Id.remove_ty v]
    | Op (_, xs) -> List.map get_occurring_arith_vars xs |> List.concat
  in
  go_hflz phi |> List.map fst

let get_guessed_terms_rep coe arg_terms term res =
  let arg_terms = List.map get_occuring_arith_terms arg_terms |> List.concat in
  let arg_terms = Hflmc2_util.remove_duplicates (=) arg_terms in
  (* let arg_terms = List.filter_map (function Arith a -> Some a | _ -> None) arg_terms in *)
  let rec go arg_terms res = 
    match arg_terms with
    | [] -> res
    | arg_term :: tail ->
      let open Arith in
      let pterm = Op(Add, [term; Op(Mult, [Int coe; arg_term])]) in
      let nterm = Op(Add, [term; Op(Mult, [Int (-coe); arg_term])]) in
      let acc =
        match arg_term with
        | Var v ->
          if is_rectvar v then
            res
          else
            pterm::nterm::res
        | Int i ->
          if i = 0 then
            res
          else
            pterm::nterm::res
        | _ -> pterm::nterm::res in
      go tail acc in
  go arg_terms res

let get_guessed_terms coe1 coe2 arg_terms =
  let const_term = Arith.Int coe2 in
  let res = get_guessed_terms_rep coe1 arg_terms const_term [const_term] in
  res

let to_ty argty basety =
  let rec go argty = match argty with
    | [] -> basety
    | x::xs -> Type.TyArrow (x, go xs) in
  go argty

let is_pred pvar =
  String.length pvar.Id.name >= 0 &&
  (String.uppercase_ascii @@ String.sub pvar.Id.name 0 1) = String.sub pvar.Id.name 0 1
  
let range n m =
  let rec go i =
    if i > m then []
    else i::(go (i + 1)) in
  go n

let replace_occurences
    (coe1: int)
    (coe2 : int)
    (outer_mu_funcs : (unit Type.ty Id.t * unit Type.ty Id.t list) list)
    (scoped_rec_tvars : ('a Id.t * 'b Id.t) list)
    (rec_tvars : ('a Id.t * unit Type.ty Type.arg Id.t) list)
    (rec_lex_tvars : ('a Type.arg Id.t * 'a Type.arg Id.t list) list)
    (fml : 'a Hflz.t) : 'a Hflz.t =
  let is_lexi_one = List.map (fun e -> List.length (snd e)) rec_lex_tvars |> List.for_all ((=)1) in
  let rec go (apps : Type.simple_ty t list) fml : 'a Hflz.t = 
    match fml with
    | Var pvar when is_pred pvar -> begin
      let formula_type_ids = pvar.ty |> to_args |> List.rev in
      let formula_type_terms = List.map argty_to_ty formula_type_ids in
      let guessed_terms = get_guessed_terms coe1 coe2 (apps @ formula_type_terms) in
      let arg_pvars = Env.lookup pvar outer_mu_funcs in
      let make_decrement term =
        let rec_lex_tvars = Env.lookup term rec_lex_tvars in
        let new_rec_lex_tvars =
          List.map
            (fun tvar -> (tvar, Id.gen ~name:(tvar.Id.name ^ "_n") Type.TyInt))
            rec_lex_tvars
          |> Env.create
            in
        let body =
          let a_to_i v = Arith.Var {v with Id.ty=`Int} in
          let rec go xs = match xs with
            | x1::x2::xs -> begin
              let new_x1 = Env.lookup x1 new_rec_lex_tvars in
              let new_x2 = Env.lookup x2 new_rec_lex_tvars in
              let new_xs = List.map (fun v -> v, (Env.lookup v new_rec_lex_tvars)) (x2::xs) in 
              Or (
                And (
                  Pred (Gt, [a_to_i x1; Int 1]),
                  And (
                    Pred (Ge, [a_to_i new_x1; Op (Sub, [a_to_i x1; Int 1])]),
                    List.map
                      (fun (x, new_x) -> Pred (Ge, [a_to_i new_x; a_to_i x]))
                      new_xs |>
                    formula_fold (fun a b -> And (a, b))
                  )
                ),
                And (
                  Pred (Le, [a_to_i x1; Int 1]),
                  And (
                    formula_fold
                      (fun a b -> And (a, b))
                      (List.map (fun t -> Pred (Ge, [a_to_i new_x1; t])) guessed_terms),
                    go (x2::xs)
                  )
                )
              )
            end              
            | [x1] -> begin
              let new_x1 = Env.lookup x1 new_rec_lex_tvars in
              Pred (Ge, [a_to_i new_x1; Op (Sub, [a_to_i x1; Int 1])])
            end
            | [] -> failwith "go1" in
          let imply_left = go rec_lex_tvars in
          Some (fun inner ->
            Or (
              Hflz.negate_formula imply_left,
              inner
            )), new_rec_lex_tvars |> List.map snd |> List.map (fun t -> {t with Id.ty=`Int})
        in
        body
      in
      let make_args env_guessed env =
        (* 述語 -> 再帰回数の変数 を受け取り、pvarの再帰変数は-1、ほかはそのまま適用する *)
        arg_pvars
        |> List.map
          (fun pvar' ->
            try let term = Env.lookup pvar' env in
              if Id.eq pvar' pvar then
                make_decrement term
                (* Arith.Op (Sub, [Var{term with Id.ty=`Int}; Int 1]) *)
              else
                (None, Env.lookup term rec_lex_tvars |> List.map (fun v -> {v with Id.ty=`Int}))
            with
              Not_found ->
                (None,
                  let t = Env.lookup pvar' env_guessed in
                  Env.lookup t rec_lex_tvars |> List.map (fun v -> {v with Id.ty=`Int})
                )
          )
      in
      let make_args_one env_guessed env =
        (* 述語 -> 再帰回数の変数 を受け取り、pvarの再帰変数は-1、ほかはそのまま適用する *)
        arg_pvars
        |> List.map
          (fun pvar' ->
            try let term = Env.lookup pvar' env in
              if Id.eq pvar' pvar then
                Arith.Op (Sub, [Var{term with Id.ty=`Int}; Int 1])
              else
                Var{term with ty=`Int}
            with
              Not_found -> Var {(Env.lookup pvar' env_guessed) with Id.ty=`Int})
        |> List.map (fun v -> Arith v)
      in
      (* S_j - S_i *)
      let new_pvars = List.filter (fun pvar -> not @@ Env.has pvar scoped_rec_tvars) arg_pvars in
      let new_fml =
        let ty =
          to_ty (
            List.map (fun pvar ->
              let rec_tvar = Env.lookup pvar rec_tvars in
              Env.lookup rec_tvar rec_lex_tvars
            ) arg_pvars
            |> List.flatten
          ) pvar.ty in
        Var {pvar with ty=ty} in
      let make_app new_fml (rec_vars : ((unit Type.ty t -> Type.simple_ty t) option * [> `Int ] Id.t list) list) formula_type_terms = 
        let body =
          to_app
            new_fml
            ((List.map
              (fun (_, v) -> List.map (fun v -> Arith (Var v)) v)
              rec_vars
            |> List.flatten) @ formula_type_terms) in
        let funcs = List.filter_map (fun (a, b) -> match a with Some s -> Some (s, b) | None -> None) rec_vars |> List.rev in
        funcs
        |> List.fold_left
          (fun a (tf, vs) ->
            to_forall
              (List.map (fun v -> { v with Id.ty=Type.TyInt}) vs)
              (tf a)
          ) body
      in
      if new_pvars = [] then
        if is_lexi_one then
          let rec_vars = make_args_one Env.empty scoped_rec_tvars in
          to_app new_fml rec_vars
        else
          (to_abs'
            formula_type_ids
            (
              let rec_vars = make_args Env.empty scoped_rec_tvars in
              make_app new_fml rec_vars formula_type_terms
            )
          )
      else begin
        let new_tvars = List.map (fun pvar -> Env.lookup pvar rec_tvars) new_pvars in
        let new_tvars_lex =
          List.map (fun v -> Env.lookup v rec_lex_tvars) new_tvars
          |> List.flatten in
        let havocs =
          (Core.List.cartesian_product
            (List.map (fun tvar -> Arith.Var{tvar with Id.ty=`Int}) new_tvars_lex)
            guessed_terms)
          |> List.map (fun (t1, t2) -> Pred (Lt, [t1; t2]))
          |> formula_fold (fun acc t -> Or (acc, t))
          in
        (to_abs'
          formula_type_ids
          (to_forall
            new_tvars_lex
              (Or (
                havocs,
                if is_lexi_one then
                  let rec_vars = make_args_one (Env.create (Core.List.zip_exn new_pvars new_tvars)) scoped_rec_tvars in
                  to_app
                    new_fml
                    (rec_vars @ formula_type_terms)
                else
                  let rec_vars = make_args (Env.create (Core.List.zip_exn new_pvars new_tvars)) scoped_rec_tvars in
                  make_app new_fml rec_vars formula_type_terms
              )
            )
          )
        )
      end
    end
    | App (f1,f2) ->  App (go (f2::apps) f1, go [] f2)
    | Or (f1,f2) -> Or (go [] f1, go [] f2)
    | And(f1,f2) -> And(go [] f1, go [] f2)
    | Abs(x, f1) -> Abs(x, go [] f1)
    | Forall(x, f1) -> Forall (x, go [] f1)
    | Exists(x, f1) -> Exists (x, go [] f1)
    | Bool _ | Pred _ | Arith _ | Var _ -> fml in
  go [] fml

let remove_duplicate_bounds (phi : Type.simple_ty Hflz.t) =
  let rec go phi = match phi with
    | Bool _ | Var _ | Arith _ | Pred _ -> phi
    | Or (p1, p2) -> begin
      (* remove duplicate of the form "pred_1 || pred_2 || ... || pred_n" *)
      let rec sub phi = match phi with
        | Pred (_, [_; _]) -> [phi]
        | Or (p1, p2) -> begin
          let a1 = sub p1 in
          let a2 = sub p2 in
          match a1, a2 with
          | [], _ -> []
          | _, [] -> []
          | _ -> a1 @ a2
        end
        | _ -> []
      in
      match sub phi with
      | [] -> Or (go p1, go p2)
      | xs -> begin
        let xs =
          if !simplify_bound then
            Simplify_bound.simplify_bound_with_z3 xs
          else
            Hflmc2_util.remove_duplicates (=) xs
        in
        formula_fold (fun acc f -> Or (acc, f)) xs
      end
    end
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p2) -> Abs (x, go p2)
    | Forall (x, p2) -> Forall (x, go p2)
    | Exists (x, p2) -> Exists (x, go p2)
    | App (p1, p2) -> App (go p1, go p2)
  in 
  go phi

let elim_mu_with_rec (entry, rules) coe1 coe2 lexico_pair_number =
  (* calc outer_mu_funcs *)
  let rules = (Hflz.mk_entry_rule entry)::rules in
  let outer_mu_funcs = get_outer_mu_funcs rules in
  (* make tvars *)
  let rec_tvars =
    rules
    |> List.filter_map
      (fun {fix; var=pvar; _} ->
        if fix = Fixpoint.Least then
          Some (pvar, rectvar_of_pvar pvar)
        else None)
    |> Env.create in
  let lexico_pair_number =
    Env.create @@ List.map (fun (_, tvar) -> (tvar, lexico_pair_number)) rec_tvars in
  let rec_lex_tvars =
    List.map
      (fun (_, rec_tvar) ->
        (
          rec_tvar,
          range 1 (Env.lookup rec_tvar lexico_pair_number)
          |> List.map (fun i -> 
            if i = 1 then rec_tvar
            else Id.gen ~name:(rec_tvar.name ^ "_" ^ string_of_int i) (Type.TyInt)
          )
        )
      )
      rec_tvars |>
    Env.create in
  (* make new hes *)
  let rules = List.map
    (fun {var=mypvar; body; _} ->
      let outer_pvars = Env.lookup mypvar outer_mu_funcs in
      let scoped_rec_tvars =
        Env.create (List.map (fun pvar -> (pvar, (Env.lookup pvar rec_tvars))) outer_pvars) in
      let body = replace_occurences coe1 coe2 outer_mu_funcs scoped_rec_tvars rec_tvars rec_lex_tvars body in
      (* Log.app begin fun m -> m ~header:"body" "%a" Print.(hflz simple_ty_) body end; *)
      let formula_type_vars = Hflz_util.get_hflz_type body |> to_args |> List.rev in
      (* 残りに受け取る引数をいったんlambdaで「受ける」 *)
      let rec_tvar_bounds' =
        List.map snd scoped_rec_tvars |>
        List.map (fun v -> Env.lookup v rec_lex_tvars) |>
        List.flatten
        in
      let body = 
        to_app
          body @@
          List.map
            argty_to_ty
            formula_type_vars in
      (* add rec > 0 if need *)
      (* if needというのは、mypvarをtopとするループがあるとき *)
      let body =
        if Env.has mypvar scoped_rec_tvars then
          let mytvar = Env.lookup mypvar scoped_rec_tvars in
          let mytvars = Env.lookup mytvar rec_lex_tvars in
          to_abs'
            (rec_tvar_bounds' @ formula_type_vars) @@
            (
              And (
                List.map
                  (fun mytvar ->
                    Pred (Gt, [Var {mytvar with ty=`Int}; Int 0])
                  )
                  mytvars |>
                formula_fold
                  (fun a b -> And (a, b)),
                body
              )
            )
        else
          to_abs'
            (rec_tvar_bounds' @ formula_type_vars)
            body
      in
      let mypvar =
        let ty =
          to_ty (
            List.map
              (fun pvar ->
                let rec_tvar = Env.lookup pvar rec_tvars in
                Env.lookup rec_tvar rec_lex_tvars
              )
              outer_pvars
            |> List.flatten
          ) mypvar.ty in
        {mypvar with ty=ty} in
      (* Log.app begin fun m -> m ~header:"body (before beta)" "%a" Print.(hflz simple_ty_) body end;
      Log.app begin fun m -> m ~header:"body (after beta)" "%a" Print.(hflz simple_ty_) (beta body) end; *)
      {fix=Greatest; var=mypvar; body=body |> beta |> remove_duplicate_bounds}
    )
    rules
  in
  let hes = Hflz.decompose_entry_rule rules in
  type_check hes;
  hes


let encode_body_forall_formula_sub new_pred_name_cand hes_preds hfl = 
  let open Type in
  let formula_type_vars = Hflz_util.get_hflz_type hfl |> to_args |> List.rev in
  (* get free variables *)
  let free_vars =
    Hflz.fvs_with_type hfl
    |> Id.remove_vars hes_preds in
  let bound_vars, hfl =
      (* sequence of universally bound variables *)
    let rec go acc hfl = match hfl with
      | Forall (x, hfl) -> go (x::acc) hfl
      | _ -> (acc, hfl) in
    let (bound_vars, hfl) = go [] hfl in
    (* ensure all variables are integer type (or not used) *)
    bound_vars |>
    List.rev |>
    List.filter_map (fun var -> 
      match var.Id.ty with
      | TyInt ->
        Some var
      | TySigma _ -> begin
        if (Hflz.fvs_with_type hfl
          |> List.exists (fun fv -> Id.eq fv var))
          then failwith "encode_body_forall_formula_sub: higher-order bound variable is not supported";
        (* when variable is not used *)
        None
      end
    ), hfl in
  let arg_vars' = free_vars @ formula_type_vars in
  let new_pvar =
    let i = Id.gen_id() in
    let name =
      match new_pred_name_cand with
      | None -> "Forall" ^ string_of_int i
      | Some p -> p ^ "_a" ^ string_of_int i in
    let ty =
      (* TODO: higher-order vars *)
      to_tree
        (arg_vars' @ bound_vars)
        (fun x rem -> TyArrow (x, rem))
        (TyBool ())  in
    { Id.name = name; ty = ty; id = i } in
  let body =
    rev_abs (
      (formula_type_vars |> List.rev |> to_abs') @@
        ((args_hfl_to_apps ((List.map arg_id_to_var arg_vars') @ List.map (fun _ -> Arith (Int 0)) bound_vars)) @@ (Var new_pvar))
        ) in
  body,
  [{ 
    Hflz.var = new_pvar;
    fix = Fixpoint.Greatest;
    body =
      ((arg_vars' @ bound_vars) |> to_abs') @@
      And (
        args_ids_to_apps formula_type_vars hfl,
        let inc_var var bound_vars is_minus =
          List.map (fun v -> if Id.eq v var then (Arith (Op ((if is_minus then Sub else Add), [Var {v with ty=`Int}; Int 1]))) else Arith (Var {v with ty=`Int})) bound_vars in
        bound_vars |>
        List.map (fun var ->
          let rec_pred is_minus =
            (List.map arg_id_to_var arg_vars') @ (inc_var var bound_vars is_minus) |>
            List.fold_left
              (fun acc t -> App (acc, t))
              (Var new_pvar) in
          And (rec_pred false, rec_pred true)
        ) |>
        formula_fold (fun acc t -> And (acc, t))
      )
  }]


let encode_body_forall_formula new_pred_name_cand hes_preds hfl =
  let new_rules = ref [] in
  let rec go hes_preds hfl = match hfl with
    | Var _ | Bool _ -> hfl
    | Or (f1, f2)  -> Or  (go hes_preds f1, go hes_preds f2)
    | And (f1, f2) -> And (go hes_preds f1, go hes_preds f2)
    | Abs (v, f1)  -> Abs (v, go hes_preds f1)
    | Forall (v, f1) -> begin
      if v.ty <> Type.TyInt then (
        (* boundされている変数の型が整数以外 *)
        match IdSet.find (fvs f1) ~f:(fun i -> Id.eq i v) with
        | None ->
          (* boundされている変数が使用されない、つまり無駄なboundなので無視 *)
          go hes_preds f1
        | Some x -> failwith "quantifiers for higher-order variables are not implemented"
      ) else (
        let hfl, rules = encode_body_forall_formula_sub new_pred_name_cand hes_preds hfl in
        let new_rule_vars = List.map (fun rule -> { rule.var with ty = Type.TySigma rule.var.ty }) rules in
        let rules = List.map (fun rule -> { rule with body = go (new_rule_vars @ hes_preds) rule.body } ) rules in
        new_rules := rules @ !new_rules;
        hfl
      )
    end
    | Exists (v, f1) -> Exists (v, go hes_preds f1)
    | App (f1, f2) -> App (go hes_preds f1, go hes_preds f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t) in
  let hfl = go hes_preds hfl in
  hfl, !new_rules

(* hesからforallを除去 *)
let encode_body_forall_except_top (hes : Type.simple_ty Hflz.hes) =
  let (entry, rules) = hes in
  let env = List.map (fun {var; _} -> { var with ty=Type.TySigma var.ty }) rules in
  let hes =
    rules |>
    List.map
      (fun {var; fix; body} -> 
        let new_pred_name_cand = Some var.name in
        let body, new_rules = encode_body_forall_formula new_pred_name_cand env body in
        {var; fix; body}::new_rules
      )
    |> List.flatten in
  (entry, hes)



let%expect_test "encode_body_forall_formula_sub" =
  let open Type in
  let p = id_n 10 (TySigma (TyArrow (id_n 12 TyInt, (TyArrow (id_n 11 TyInt, TyBool ()))))) in
  (* 高階変数の扱い *)
  (* その時点で使える自由変数ということは、直前のラムダ抽象も含まれる？ => いや、そこは使わない。あくまで式の中の型を取得するだけなので、別。free var のみを使用 *)
  (* ∃x_100.∃x_300.λx_1:int.λx_2:(int -> bool).(x_10 :int -> int -> bool) (x_1 + x_3) x_300 && (x_2:int -> bool) x_5 && (x_4:int -> bool) x_100 *)
  (* other predicates = x10 : int -> bool *)
  (* arguments in the term's type = x1 : int, x2 : int -> bool *)
  (* free variables = x3 : int, x4 : int -> bool, x5 : int *)
  let org_formula =
    Forall (id_n 100 TyInt, Forall (id_n 300 TyInt, Abs (id_n 1 TyInt, Abs (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))),
      And (
        App (App (Var { p with ty = unsafe_unlift p.ty }, 
          Arith (Op (Add, [Var (id_n 1 `Int); Var (id_n 3 `Int)]))), Arith (Var (id_n 300 `Int))),
        And (App (Var (id_n 2 (TyArrow (id_n 31 TyInt, TyBool ()))), Arith (Var (id_n 5 `Int))),
          App (Var (id_n 4 (TyArrow (id_n 32 TyInt, TyBool ()))), Arith (Var (id_n 100 `Int)))))
      )))) in
  print_endline @@ "original: " ^ show_hflz org_formula;
  [%expect {|
    original: ∀x_100100.
     ∀x_300300.
      λx_11:int.
       λx_22:(int -> bool).
        x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100 |}];
  let (replaced, rules) =
    encode_body_forall_formula_sub
      None
      [p]
      org_formula
    in
  ignore [%expect.output];
  print_endline @@ string_of_int @@ List.length rules;
  let rule = List.nth rules 0 in
  print_endline @@ "replaced: " ^ show_hflz replaced;
  [%expect {|
    1
    replaced: λx_11:int.λx_22:(int -> bool).Forall0 x_33 x_44 x_55 x_11 x_22 0 0  |}];
  print_endline @@ "fix: " ^ Fixpoint.show rule.fix;
  print_endline @@ "var: " ^ Id.show pp_simple_ty rule.var;
  print_endline @@ "rule: " ^ show_hflz rule.body;
  [%expect {|
    fix: Fixpoint.Greatest
    var: { Id.name = "Forall0"; id = 0;
      ty =
      (Type.TyArrow ({ Id.name = "x_3"; id = 3; ty = Type.TyInt },
         (Type.TyArrow (
            { Id.name = "x_4"; id = 4;
              ty =
              (Type.TySigma
                 (Type.TyArrow ({ Id.name = "x_32"; id = 32; ty = Type.TyInt },
                    (Type.TyBool ()))))
              },
            (Type.TyArrow ({ Id.name = "x_5"; id = 5; ty = Type.TyInt },
               (Type.TyArrow ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
                  (Type.TyArrow (
                     { Id.name = "x_2"; id = 2;
                       ty =
                       (Type.TySigma
                          (Type.TyArrow (
                             { Id.name = "x_31"; id = 31; ty = Type.TyInt },
                             (Type.TyBool ()))))
                       },
                     (Type.TyArrow (
                        { Id.name = "x_100"; id = 100; ty = Type.TyInt },
                        (Type.TyArrow (
                           { Id.name = "x_300"; id = 300; ty = Type.TyInt },
                           (Type.TyBool ())))
                        ))
                     ))
                  ))
               ))
            ))
         ))
      }
    rule: λx_33:int.
     λx_44:(int -> bool).
      λx_55:int.
       λx_11:int.
        λx_22:(int -> bool).
         λx_100100:int.
          λx_300300:int.
           (λx_11:int.
             λx_22:(int -> bool).
              x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100)
            x_11 x_22
           && Forall0 x_33 x_44 x_55 x_11 x_22 (x_100100 + 1) x_300300
              && Forall0 x_33 x_44 x_55 x_11 x_22 (x_100100 - 1) x_300300
              && Forall0 x_33 x_44 x_55 x_11 x_22 x_100100 (x_300300 + 1)
                 && Forall0 x_33 x_44 x_55 x_11 x_22 x_100100 (x_300300 - 1)|}];
  (* check well-typedness *)
  let rules = [
    {
      var = id_n 200 (TyArrow (id_n 3 TyInt, TyArrow (id_n 4 @@ TySigma (TyArrow (id_n 32 TyInt, TyBool ())),
        TyArrow (id_n 5 TyInt, TyArrow (id_n 1 TyInt, (TyArrow (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))), TyBool ())))))));
      fix = Fixpoint.Greatest;
      body = Abs (id_n 3 TyInt, Abs (id_n 4 (TySigma (TyArrow (id_n 32 TyInt, TyBool ()))), Abs (id_n 5 TyInt, replaced))) };
    {
      var = { p with ty = unsafe_unlift p.ty};
      body = Abs (id_n 12 TyInt, Abs (id_n 11 TyInt, Bool true));
      fix = Fixpoint.Greatest };
    rule ] in
  let hes = Bool true, rules in
  let hes = decompose_lambdas_hes hes in
  type_check hes;
  ignore [%expect.output];
  print_endline "OK";
  [%expect {|OK|}]
