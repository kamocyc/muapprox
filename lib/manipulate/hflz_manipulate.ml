module Print = Print_syntax
module Fixpoint = Hflmc2_syntax.Fixpoint
module Formula = Hflmc2_syntax.Formula
module IdSet = Hflmc2_syntax.IdSet
module Eliminate_unused_argument = Eliminate_unused_argument

open Hflz_typecheck
open Hflz

(* module Util = Hflmc2_util *)

let simplify_bound = ref false

let show_hflz = Print.show_hflz

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

let log_string = Hflz_util.log_string Log.info

(* Arrow type to list of types of the arguments conversion *)
(* t1 -> t2 -> t3  ==> [t3; t2; t1]  *)
let to_args : Type.simple_ty -> Type.simple_ty Type.arg Id.t list =
  let rec go =
    fun acc ty -> match ty with
    | Type.TyArrow (arg, ty) -> go (arg::acc) ty
    | Type.TyBool _ -> acc in
  go []

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

let to_app inner terms =
  let rec go terms = match terms with
    | t::ts -> App (go ts, t)
    | [] -> inner in
  go @@ List.rev terms

let argty_to_var {Id.name; id; ty} =
  match ty with
  | Type.TyInt -> 
    Arith (Var {name; id; ty=`Int})
  | Type.TySigma x -> 
    Var {name; id; ty=x}
  
let formula_fold func terms = match terms with
    | [] -> failwith "[formula_fold] Number of elements should not be zero."
    | term::terms -> begin
      List.fold_left func term terms
    end

let make_approx_formula fa_var_f bounds = 
  bounds
  |> List.map (fun bound -> Pred (Lt, [Var fa_var_f; bound]))
  |> formula_fold (fun acc f -> Or (acc, f))

(* abstractioの順序を逆にする *)
let rev_abs hflz =
  let rec get_abs acc hflz =
    match hflz with
    | Abs (x, hflz) ->
      get_abs (x::acc) hflz
    | _ -> (hflz, acc) in
  let (body, vars) = get_abs [] hflz in
  to_abs' vars body

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
      (* Log.info begin fun m -> m ~header:("Abs") "%a"
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
        (* Log.info begin fun m -> m ~header:("Forall 前" ^ x.name) "%a"
          Print.(hflz simple_ty_) new_rule.body
        end; *)
        let new_rule = { new_rule with body = in_forall @@ mk_quant quant_acc new_rule.body } in
        (* Log.info begin fun m -> m ~header:("Forall 後" ^ x.name) "%a"
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
  (* Log.info begin fun m -> m ~header:"original formula" "%a"
    Print.(hflz simple_ty_) phi
  end; *)
  let res = go' phi in
  (* Log.info begin fun m -> m ~header:"converted formula" "%a"
    Print.(hflz simple_ty_) res
  end;
  Log.info begin fun m -> m ~header:"added_rules" "%a"
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
  let rules = merge_entry_rule (entry, rules) in
  let rules = rules |> List.map (decompose_lambdas hes_names) |> List.flatten in
  (* Hflz.decompose_entry_rule rules |> (Hflz_util.with_rules Hflz_util.assign_unique_variable_id) *)
  Hflz.decompose_entry_rule rules


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

let get_occuring_arith_terms id_type_map phi = 
  (* remove expressions that contain locally bound variables *)
  let remove ls x =
    List.filter (fun (_, vars) -> not @@ List.exists ((=) (Id.remove_ty x)) vars) ls
  in
  let rec go_hflz phi = match phi with
    | Bool _ -> []
    | Var _ -> [] (* use only arithmetic variable *)
    | Or (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | And (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Abs (x, p1) -> remove (go_hflz p1) x
    | Forall (x, p1) -> remove (go_hflz p1) x
    | Exists (x, p1) -> remove (go_hflz p1) x
    | App (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Arith (a) -> [(a, get_occurring_arith_vars a)]
    | Pred (p, xs) -> begin
      match p, xs with
      | Lt, [Var x; _] when Hflmc2_syntax.IdMap.mem id_type_map (Id.remove_ty x) -> []
      | _ -> List.map (fun a -> (a, get_occurring_arith_vars a)) xs
    end
  and get_occurring_arith_vars phi = match phi with
    | Int _ -> []
    | Var v -> [Id.remove_ty v]
    | Op (_, xs) -> List.map get_occurring_arith_vars xs |> List.concat
  in
  go_hflz phi |> List.map fst

let get_guessed_terms id_type_map arg_terms scoped_variables id_ho_map =
  let open Hflmc2_syntax in
  let all_terms =
    (List.map (get_occuring_arith_terms id_type_map) arg_terms |> List.concat) @
    (List.filter_map
      (fun var -> match var.Id.ty with
        | Type.TyInt -> Some (Arith.Var {var with Id.ty = `Int})
        | _ -> None
      )
      scoped_variables) @
    (
      List.map Hflz.fvs_with_type arg_terms
      |> List.concat
      |> List.filter_map (fun var -> match var.Id.ty with
        | Type.TySigma _ -> begin
          match List.find_opt (fun (id, _) -> Id.eq id var) id_ho_map with
          | Some (_, id_i) -> Some (Arith.Var id_i)
          | None -> None
        end
        | Type.TyInt -> None
      )
    )
  in
  all_terms
  |> List.map
    (fun (arg_term : Arith.t) -> match arg_term with
      | Var v ->
        if is_rectvar v then
          []
        else
          [arg_term]
      | Int i ->
        if i = 0 then
          []
        else
          [arg_term]
      | _ -> [arg_term]
    )
  |> List.flatten
  |> Hflmc2_util.remove_duplicates (=)
  
  
let get_guessed_conditions_rep coe arg_terms term =
  arg_terms
  |> List.rev
  |> List.map
    (fun arg_term -> 
      let open Arith in
      let pterm = Op(Add, [term; Op(Mult, [Int coe; arg_term])]) in
      let nterm = Op(Add, [term; Op(Mult, [Int (-coe); arg_term])]) in
      pterm :: [nterm]
    )
  |> List.flatten

let get_guessed_conditions coe1 coe2 guessed_terms =
  let const_term = Arith.Int coe2 in
  let res = (get_guessed_conditions_rep coe1 guessed_terms const_term) @ [const_term] in
  res

let to_ty argty basety =
  let rec go argty = match argty with
    | [] -> basety
    | x::xs -> Type.TyArrow (x, go xs) in
  go argty

let get_dual_hes ((entry, rules) : Type.simple_ty hes): Type.simple_ty hes =
  let entry = Hflz.negate_formula entry in
  let results = List.map (fun rule -> Hflz.negate_rule rule) rules in
  let hes = (entry, results) in
  Log.info begin fun m -> m ~header:"get_dual_hes" "%a" Print.(hflz_hes simple_ty_) hes end;
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

let rec to_tree seq f b = match seq with
  | [] -> b
  | x::xs -> f x (to_tree xs f b)


  
let encode_body_exists_formula_sub new_pred_name_cand coe1 coe2 hes_preds hfl (id_type_map : (unit Id.t, Hflz_util.variable_type, Hflmc2_syntax.IdMap.Key.comparator_witness) Base.Map.t) id_ho_map use_all_scoped_variables env = 
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
    (* ensure all variables are integer type (otherwise, error) *)
    bound_vars |>
    List.rev |>
    List.filter_map (fun var -> 
      match var.Id.ty with
      | TyInt ->
        Some var
      | TySigma _ -> begin
        if (Hflz.fvs_with_type hfl
          |> List.exists (fun fv -> Id.eq fv var))
          then failwith "encode_body_exists_formula_sub: higher-order quantified variable is not supported";
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
      to_tree
        arg_vars
        (fun x rem -> TyArrow (x, rem))
        (TyBool ()) in
    { Id.name = name; ty = ty; id = i } in
  let body =
    let guessed_conditions =
      log_string @@ "[encode_body_exists_formula_sub.guessed_conditions] body: " ^ show_hflz hfl;
      log_string @@ Hflmc2_util.show_list (fun (t, id) -> "(" ^ t.Id.name ^ ", " ^ id.Id.name ^ ")") id_ho_map;
      let id_type_map' =
        Hflmc2_syntax.IdMap.fold
          ~init:[]
          ~f:(fun ~key ~data acc ->
            match data with
            | VTHigherInfo xs_opt -> begin
              match xs_opt with
              | Some (k, xs) ->
                assert (Id.eq k key);
                ((List.map (fun v -> (v, {key with ty = `Int})) xs)::acc)
              | None -> acc
            end
            | VTVarMax _ -> acc
          )
          id_type_map
        |> List.flatten in
      log_string @@ Hflmc2_util.show_list (fun (t, id) -> "(" ^ t.Id.name ^ ", " ^ id.Id.name ^ ")") id_type_map';
      let guessed_terms =
        get_guessed_terms id_type_map [hfl] (if use_all_scoped_variables then env else []) (id_ho_map @ id_type_map')
        |> List.map (fun arith_t ->
          let fvs = Hflz.fvs (Arith arith_t) in
          let bound_vars, not_bound_vars =
            IdSet.partition_tf ~f:(fun id -> List.exists (fun bound_var -> Id.eq bound_var id) bound_vars) fvs in
          if IdSet.is_empty bound_vars then
            [arith_t]
          else
            IdSet.fold not_bound_vars ~init:[] ~f:(fun acc x -> (Arith.Var {x with ty=`Int})::acc)
        )
        |> List.concat
        |> Hflmc2_util.remove_duplicates (=) in
      log_string @@ "guessed_terms: " ^ (List.map (fun rr -> (show_hflz (Arith rr))) guessed_terms |> String.concat ",");
      get_guessed_conditions coe1 coe2 guessed_terms in
    
    (* 各要素が x < 1 + c \/ ... という形式 *)
    let approx_formulas =
      bound_vars
      |> List.rev
      |> List.map (fun bound_var ->
        make_approx_formula
          {bound_var with ty=`Int}
          guessed_conditions
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
          (* NOTE: exponential blow-up *)
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

let encode_body_exists_formula new_pred_name_cand coe1 coe2 hes_preds hfl id_type_map id_ho_map use_all_scoped_variables =
  let new_rules = ref [] in
  let rec go env hes_preds hfl = match hfl with
    | Var _ | Bool _ -> hfl
    | Or (f1, f2)  -> Or  (go env hes_preds f1, go env hes_preds f2)
    | And (f1, f2) -> And (go env hes_preds f1, go env hes_preds f2)
    | Abs (v, f1)  -> Abs (v, go (v::env) hes_preds f1)
    | Forall (v, f1) -> Forall (v, go (v::env) hes_preds f1)
    | Exists (v, f1) -> begin
      if v.ty <> Type.TyInt then (
        (* boundされている変数の型が整数以外 *)
        match IdSet.find (fvs f1) ~f:(fun i -> Id.eq i v) with
        | None ->
          (* boundされている変数が使用されない、つまり無駄なboundなので無視 *)
          go (v::env) hes_preds f1
        | Some x -> failwith @@ "quantifiers for higher-order variables are not implemented (" ^ x.name ^ ")"
      ) else (
        let hfl, rules = encode_body_exists_formula_sub new_pred_name_cand coe1 coe2 hes_preds hfl id_type_map id_ho_map use_all_scoped_variables env in
        let new_rule_vars = List.map (fun rule -> { rule.var with ty = Type.TySigma rule.var.ty }) rules in
        let rules = List.map (fun rule -> { rule with body = go [] (new_rule_vars @ hes_preds) rule.body } ) rules in
        new_rules := rules @ !new_rules;
        hfl
      )
    end
    | App (f1, f2) -> App (go env hes_preds f1, go env hes_preds f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t) in
  let hfl = go [] hes_preds hfl in
  hfl, !new_rules

(* hesからexistentialを除去 *)
let encode_body_exists
    (coe1 : int)
    (coe2 : int)
    (hes : Hflmc2_syntax.Type.simple_ty Hflz.hes)
    (id_type_map : (unit Print.Id.t, Hflz_util.variable_type, Hflmc2_syntax.IdMap.Key.comparator_witness) Hflmc2_util.Map.t)
    (id_ho_map : ('b Print.Id.t * [ `Int ] Print.Id.t) list)
    (use_all_scoped_variables : bool) =
  let (entry, rules) = hes in
  let env = List.map (fun {var; _} -> { var with ty=Type.TySigma var.ty }) rules in
  let entry, new_rules = encode_body_exists_formula None coe1 coe2 env entry id_type_map id_ho_map use_all_scoped_variables in
  let rules =
    rules |>
    List.map
      (fun {var; fix; body} -> 
        let body, new_rules = encode_body_exists_formula (Some var.name) coe1 coe2 env body id_type_map id_ho_map use_all_scoped_variables in
        {var; fix; body}::new_rules
      )
    |> List.flatten in
  (* (entry, new_rules @ rules) |> (Hflz_util.with_rules Hflz_util.assign_unique_variable_id) *)
  (entry, new_rules @ rules)


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
  
let range n m =
  let rec go i =
    if i > m then []
    else i::(go (i + 1)) in
  go n

(* for replace_occurences *)
let make_decrement rec_lex_tvars guessed_conditions term  =
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
                (List.map (fun t -> Pred (Ge, [a_to_i new_x1; t])) guessed_conditions),
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
    
let replace_occurences
    (coe1: int)
    (coe2 : int)
    (outer_mu_funcs : (unit Type.ty Id.t * unit Type.ty Id.t list) list)
    (scoped_rec_tvars : ('a Id.t * 'b Id.t) list)
    (rec_tvars : ('a Id.t * unit Type.ty Type.arg Id.t) list)
    (rec_lex_tvars : ('a Type.arg Id.t * 'a Type.arg Id.t list) list)
    id_type_map
    use_all_scoped_variables
    id_ho_map
    (fml : 'a Hflz.t) : 'a Hflz.t =
  let is_lexi_one = List.map (fun e -> List.length (snd e)) rec_lex_tvars |> List.for_all ((=)1) in
  let rec go env (apps : Type.simple_ty t list) fml : 'a Hflz.t = 
    match fml with
    | Var pvar when Id.is_pred_name pvar.Id.name -> begin
      let formula_type_ids = pvar.ty |> to_args |> List.rev in
      let id_ho_map = id_ho_map @
        (if List.length apps = List.length formula_type_ids then begin
          (* appsが単なる変数のときは、対応関係を取得 *)
          (* TODO: 順番があっている？ *)
          let assoc =
            List.combine (List.rev apps) formula_type_ids
            |> List.filter_map (fun (app, id) ->
              match app with
              | Var id' ->
                Some (Id.remove_ty id, id')
              | _ -> None
            )
            |> List.filter_map (fun (id, id_app) ->
              match List.find_opt (fun (id_ho, _) -> Id.eq id_ho id_app) id_ho_map with
              | Some (_, id_i) -> Some (Id.remove_ty id, id_i)
              | None -> None
            )
            in
          assoc
        end else []) in
      let formula_type_terms = List.map argty_to_var formula_type_ids in
      let guessed_conditions =
        let guessed_terms =
          get_guessed_terms id_type_map (apps @ formula_type_terms) (if use_all_scoped_variables then env else []) id_ho_map in
        get_guessed_conditions coe1 coe2 guessed_terms in
      let arg_pvars =
        try
          Env.lookup pvar outer_mu_funcs
        with Not_found ->
          print_endline @@ "pvar: " ^ pvar.Id.name;
          raise Not_found
        in
      let make_args env_guessed env =
        (* when lexicographic order *)
        (* 述語 -> 再帰回数の変数 を受け取り、pvarの再帰変数は-1、ほかはそのまま適用する *)
        arg_pvars
        |> List.map
          (fun pvar' ->
            try let term = Env.lookup pvar' env in
              if Id.eq pvar' pvar then
                make_decrement rec_lex_tvars guessed_conditions term
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
        (* when not lexicographic order *)
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
        (* ∀r. r < 1 + x \/ ... \/ A r x ... *)
        let havocs =
          (Core.List.cartesian_product
            (List.map (fun tvar -> Arith.Var{tvar with Id.ty=`Int}) new_tvars_lex)
            guessed_conditions)
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
    | App (f1,f2) ->  App (go env (f2::apps) f1, go env [] f2)
    | Or (f1,f2) -> Or (go env [] f1, go env [] f2)
    | And(f1,f2) -> And(go env [] f1, go env [] f2)
    | Abs(x, f1) -> Abs(x, go (x::env) [] f1)
    | Forall(x, f1) -> Forall (x, go (x::env) [] f1)
    | Exists(x, f1) -> Exists (x, go (x::env) [] f1)
    | Bool _ | Pred _ | Arith _ | Var _ -> fml in
  go [] [] fml

let remove_duplicate_bounds z3_path (phi : Type.simple_ty Hflz.t) =
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
            Hflmc2_util.remove_duplicates (=) xs
            |> Simplify_bound.simplify_bound_with_z3 z3_path
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

let get_occurring_variables_in_arith a =
  let rec go a = match a with
    | Arith.Var v -> [v]
    | Op (_, xs) -> List.map go xs |> List.flatten
    | Int _ -> []
  in
  go a
  
let substitute_arith a (before, after) =
  let rec go a = match a with
    | Arith.Var v -> begin
      if Id.eq v before then after else Arith.Var v
    end
    | Int i -> Int i
    | Op (op, xs) -> Op (op, List.map go xs)
  in
  go a
      
    
let remove_redundant_bounds id_type_map (phi : Type.simple_ty Hflz.t) =
  let rec go phi = match phi with
    | Bool _ | Var _ | Arith _ | Pred _ -> phi
    | Or (p1, p2) -> begin
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
      | bounds -> begin
        let bounds =
          List.map 
            (fun bound -> match bound with
              | Pred (Lt, [Var rec_v; rhs]) -> begin
                let vs = get_occurring_variables_in_arith rhs in
                match vs with
                | [v] -> begin
                  match Hflmc2_syntax.IdMap.find id_type_map v with
                  | Some var_category -> begin
                    match var_category with
                    | Hflz_util.VTVarMax ariths -> begin
                      (* 整数変数のMAXを表す変数vの場合、vが集約している変数を直接利用する *)
                      match ariths with
                      | [] -> [Pred (Lt, [Var rec_v; substitute_arith rhs (v, Int 0)])]
                      | _ ->
                        List.map
                          (fun a ->
                            Pred (Lt, [Var rec_v; substitute_arith rhs (v, a)])
                          )
                          ariths
                    end
                    | Hflz_util.VTHigherInfo _ -> [bound]
                  end
                  | None -> [bound]
                end
                | _ -> [bound]
              end
              | _ -> [bound]
            )
            bounds
          |> List.flatten in
        formula_fold (fun acc f -> Or (acc, f)) bounds
      end
    end
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p2) -> Abs (x, go p2)
    | Forall (x, p2) -> Forall (x, go p2)
    | Exists (x, p2) -> Exists (x, go p2)
    | App (p1, p2) -> App (go p1, go p2)
  in 
  go phi
   
let elim_mu_with_rec (entry, rules) coe1 coe2 lexico_pair_number id_type_map use_all_scoped_variables id_ho_map z3_path =
  (* calc outer_mu_funcs *)
  let rules = Hflz.merge_entry_rule (entry, rules) in
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
      let body = replace_occurences coe1 coe2 outer_mu_funcs scoped_rec_tvars rec_tvars rec_lex_tvars id_type_map use_all_scoped_variables id_ho_map body in
      (* Log.info begin fun m -> m ~header:"body" "%a" Print.(hflz simple_ty_) body end; *)
      let formula_type_vars = Hflz_util.get_hflz_type body |> to_args |> List.rev in
      let rec_tvar_bounds' =
        List.map snd scoped_rec_tvars |>
        List.map (fun v -> Env.lookup v rec_lex_tvars) |>
        List.flatten
        in
      let body = 
        to_app
          body @@
          List.map
            argty_to_var
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
      let id_type_map, body' = Hflz_util.beta id_type_map body in
      (* print_endline "body (before beta)";
      print_endline @@ Hflmc2_util.fmt_string Print.(hflz simple_ty_) body;
      print_endline "body (after beta)";
      print_endline @@ Hflmc2_util.fmt_string Print.(hflz simple_ty_) body';
      print_endline "body (after beta 2)";
      print_endline @@ Hflmc2_util.fmt_string Print.(hflz simple_ty_) (body' |> (remove_redundant_bounds id_type_map) |> remove_duplicate_bounds); *)
      (* print_endline "body (after beta 3)";
      print_endline @@ Hflmc2_util.fmt_string Print.(hflz simple_ty_) (body |> (remove_redundant_bounds id_type_map) |> Hflz_util.beta |> remove_duplicate_bounds); *)
      (* print_endline "body (after beta 4)";
      print_endline @@ Hflmc2_util.fmt_string Print.(hflz simple_ty_) (body |> (remove_redundant_bounds id_type_map) |> Hflz_util.beta |> (remove_redundant_bounds id_type_map) |> remove_duplicate_bounds); *)
      {fix=Greatest; var=mypvar; body=body' |> (remove_redundant_bounds id_type_map) |> remove_duplicate_bounds z3_path}
    )
    rules
  in
  let hes = Hflz.decompose_entry_rule rules in
  type_check hes;
  (* hes |> (Hflz_util.with_rules Hflz_util.assign_unique_variable_id) *)
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
        | Some _ -> failwith "quantifiers for higher-order variables are not implemented"
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
  (* (entry, hes) |> (Hflz_util.with_rules Hflz_util.assign_unique_variable_id) *)
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
    Forall (id_n 100 TyInt, Forall (id_n 300 TyInt,
      App (
        App (
          Abs (id_n 1 TyInt, Abs (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))),
            And (
              App (App (Var { p with ty = unsafe_unlift p.ty }, 
                Arith (Op (Add, [Var (id_n 1 `Int); Var (id_n 3 `Int)]))), Arith (Var (id_n 300 `Int))),
              And (App (Var (id_n 2 (TyArrow (id_n 31 TyInt, TyBool ()))), Arith (Var (id_n 5 `Int))),
                App (Var (id_n 4 (TyArrow (id_n 32 TyInt, TyBool ()))), Arith (Var (id_n 100 `Int)))))
            )
          ),
          Arith (Int 1)
        ),
        Abs (id_n 41 TyInt, Pred (Eq, [Var (id_n 41 `Int); Int 2]))
      )
     )
    ) in
  print_endline @@ "original: " ^ show_hflz org_formula;
  [%expect {|
    original: ∀x_100100.
     ∀x_300300.
      (λx_11:int.
        λx_22:(int -> bool).
         x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100)
       1 (λx_4141:int.x_4141 = 2)|}];
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
    replaced: Forall0 x_33 x_44 x_55 0 0  |}];
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
               (Type.TyArrow ({ Id.name = "x_100"; id = 100; ty = Type.TyInt },
                  (Type.TyArrow (
                     { Id.name = "x_300"; id = 300; ty = Type.TyInt },
                     (Type.TyBool ())))
                  ))
               ))
            ))
         ))
      }
    rule: λx_33:int.
     λx_44:(int -> bool).
      λx_55:int.
       λx_100100:int.
        λx_300300:int.
         (λx_11:int.
           λx_22:(int -> bool).
            x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100)
          1 (λx_4141:int.x_4141 = 2)
         && Forall0 x_33 x_44 x_55 (x_100100 + 1) x_300300
            && Forall0 x_33 x_44 x_55 (x_100100 - 1) x_300300
            && Forall0 x_33 x_44 x_55 x_100100 (x_300300 + 1)
               && Forall0 x_33 x_44 x_55 x_100100 (x_300300 - 1)|}];
  (* check well-typedness *)
  let rules = [
    {
      var = id_n 200 (TyArrow (id_n 3 TyInt, TyArrow (id_n 4 @@ TySigma (TyArrow (id_n 32 TyInt, TyBool ())),
        TyArrow (id_n 5 TyInt, TyBool ()))));
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
