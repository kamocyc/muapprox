module Type = Hflmc2_syntax.Type
module Hflz = Hflmc2_syntax.Hflz
module Print = Print_syntax
module Fixpoint = Hflmc2_syntax.Fixpoint
module Formula = Hflmc2_syntax.Formula
open Hflz_typecheck
open Hflz

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

(* Arrow type to list of types of the arguments conversion *)
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
          (* TODO: これはたぶん引数の順番が逆になる *)
          App (go child, Arith (Var {name; id; ty=`Int}))
        | Type.TySigma x -> 
          App (go child, Var {name; id; ty=x})
      end
      | _ -> body in
    go hfl
    
  
  
(* A, B *)
(* 任意の組 *)
let make_bounds (coe1 : int) (coe2 : int) vars =
  let rec go (vars : [`Int] Id.t list) : Arith.t list list  = match vars with 
    | var::vars -> begin
      let results = go vars in
      let r1 = List.map (fun r -> (Arith.Op (Mult, [Int coe1; Var var])::r)) results in
      let r2 = List.map (fun r -> (Arith.Op (Mult, [Int (-coe1); Var var])::r)) results in
      r1 @ r2
    end
    | [] -> [[Arith.Int coe2]] in
  let join_with terms op = match terms with
    | [] -> failwith "join_with"
    | x::xs -> begin
      List.fold_left (fun acc f -> Arith.Op (op, [acc; f])) x xs
    end in
  let terms = go vars in
  List.map (fun term -> join_with term Arith.Add) terms

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

let replace_caller_sub coe1 coe2 env id id' =
  (* 処理対象のpredicateであるとき *)
  let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
  let new_rec_var_f = {new_rec_var with ty = `Int} in
  (* predicateの型から引数を取得 *)
  (* TODO: predicateが部分適用されているときにうまくいく？ *)
  let abs = to_abs @@ to_args id'.Id.ty in
  let vars = to_vars (abs @@ (* Dummy *) Bool true) in
  (* TODO: Int 10じゃなくてうまく決める *)
  (* negativeにしているので注意 *)
  let bound_int_vars = filter_int_variable env in
  let bounds = make_bounds coe1 coe2 bound_int_vars in
  print_int @@ List.length bounds;
  let approx_formula = make_approx_formula new_rec_var_f bounds in
  Forall (new_rec_var, abs @@ Or (approx_formula, vars @@ App (Var id, Arith (Var new_rec_var_f))))
(*        let ref_rule = get_rule id hes in
  (* TODO: forallを別途処理する *)
  let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
  let new_rec_var_f = {new_rec_var with ty = `Int} in
  let new_rule_id = Id.gen ~name:("forall_" ^ id.name) (Type.TyArrow (new_rec_var, id.ty)) in
  let new_rule = {
    var = new_rule_id;
    (* TODO: ヒューリスティックで決める *)
    body = (
      let args = to_args id.ty in
      let abs = to_abs args in
      let vars = to_vars args in
      abs @@ And (Or (Pred (Formula.Lt, [Var new_rec_var_f; Int 10]), vars @@ App (Var id, Arith (Var new_rec_var_f))), vars @@ App (Var new_rule_id, Arith (Op (Add, [Var new_rec_var_f; Int 1]))))
    );
    fix = Fixpoint.Greatest } in
  new_rules := new_rule :: !new_rules;
  App (Var new_rule_id, Arith (Int 0)) *)

(* 変換した述語の呼び出し元を置換 *)
let replace_caller (hfl : Type.simple_ty Hflz.t) (preds : Type.simple_ty Id.t list) (coe1 : int) (coe2 : int) : Type.simple_ty Hflz.t =
  let rec go env (hfl : Type.simple_ty Hflz.t) : Type.simple_ty Hflz.t = match hfl with
    | Var id' -> begin
      (* TODO: IDのeqが正しく判定される？ *)
      match List.find_opt (fun pred -> Id.eq pred id') preds with
      | Some id -> replace_caller_sub coe1 coe2 env id id'
      | None -> Var id'
    end
    | Bool   b -> Bool b
    | Or (f1, f2) -> Or (go env f1, go env f2)
    | And (f1, f2) -> And (go env f1, go env f2)
    | Abs (v, f1) -> Abs (v, go ((v)::env) f1)
    | Forall (v, f1) -> Forall (v, go ((v)::env) f1)
    | Exists (v, f1) -> Exists (v, go ((v)::env) f1)
    | App (f1, f2) -> App (go env f1, go env f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t)
  in
  (* predicateはboolean以外を返すことは無い。arithmeticの中にhfl predicateは現れない *)
  go [] hfl

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

let to_arrow_type ?base:(base=Type.TyBool ()) args  =
  let rec go acc args = match args with
    | arg::xs -> begin
      go (Type.TyArrow (arg, acc)) xs
    end
    | [] -> acc in
  go base (List.rev args)
  
 (* : Type.simple_ty Type.arg Id.t list -> Type.simple_ty *)
let args_ids_to_apps (ids : 'ty Type.arg Id.t list) : ('ty Hflz.t -> 'ty Hflz.t) = fun body ->
  let rec go ids = match ids with
    | x::xs -> begin
      match x.Id.ty with
      | Type.TySigma t -> begin
        App (go xs, Var {x with ty=t})
      end
      | Type.TyInt -> begin
        App (go xs, Arith (Var {x with ty=`Int}))
      end
    end
    | [] -> body in
  go @@ List.rev ids

let remove_elt f l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when f x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l []
  
let remove_duplicates f l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt (f x) xs) (x::acc)
  in go l []

let fvs_with_type : 'ty Hflz.t -> 'ty Type.arg Id.t list = fun hes ->
  let rec go = function
    | Var x          -> [{ x with ty = Type.TySigma x.ty}]
    | Bool _         -> []
    | Or (phi1,phi2) -> (go phi1) @ (go phi2)
    | And(phi1,phi2) -> (go phi1) @ (go phi2)
    | App(phi1,phi2) -> (go phi1) @ (go phi2)
    | Abs(x, phi)    -> List.filter (fun t -> not @@ Id.eq t x) @@ go phi(* listだと、ここが毎回線形時間になる... *)
    | Forall(x, phi) -> List.filter (fun t -> not @@ Id.eq t x) @@ go phi
    | Exists(x, phi) -> List.filter (fun t -> not @@ Id.eq t x) @@ go phi
    | Arith a        -> List.map (fun id -> {id with Id.ty = Type.TyInt}) @@ Arith.fvs a
    | Pred (_, as')   -> as' |> List.map (fun a -> Arith.fvs a |> List.map (fun id -> {id with Id.ty = Type.TyInt})) |> List.flatten in
  go hes |> remove_duplicates (fun e x -> Id.eq e x)


(* 次のレベル (=同じ種類のfixpoint) のequationsを取得 *)
let get_next_level : 'ty Hflz.hes -> ('ty Hflz.hes * 'ty Hflz.hes) =
  fun hes -> match hes with
    | [] -> ([], [])
    | _ -> begin
      let revl = List.rev hes in
      let ({fix; _}) = List.nth revl 0 in
      let rec go acc = function
        | [] -> ([], acc)
        | ({fix=fix'; _} as eq)::eqs -> 
          if fix = fix'
          then go (eq::acc) eqs
          else (eq::eqs, acc)
      in
      go [] revl
      |> (fun (l1, l2) -> (List.rev l1, List.rev l2))
    end

let get_next_mu_level : 'ty Hflz.hes -> ('ty Hflz.hes * 'ty Hflz.hes * 'ty Hflz.hes) = fun hes -> 
    let (remain_level, next_level) = get_next_level hes in
    match next_level with 
    | [] -> ([], [], [])
    | ({fix; _}::_) -> begin
      let (remain_level', next_level') = get_next_level remain_level in
      match fix with
      | Fixpoint.Greatest -> 
        (remain_level', next_level', next_level)
      | Fixpoint.Least -> 
        (remain_level, next_level, [])
    end

(* 変数の出現を置換 *)
let replace_var_occurences : ('ty Id.t -> 'ty Hflz.t) -> 'ty Hflz.t -> 'ty Hflz.t =
  fun subst hfl -> 
  (* TODO: IDのeqが正しく判定される？ *)
  let rec go = function
    | Var   id -> subst (id)
    | Bool   b -> Bool b
    | Or (f1, f2) -> Or (go f1, go f2)
    | And (f1, f2) -> And (go f1, go f2)
    | Abs (v, f1) -> Abs (v, go f1)
    | Forall (v, f1) -> Forall (v, go f1)
    | Exists (v, f1) -> Exists (v, go f1)
    | App (f1, f2) -> App (go f1, go f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t)
  in
  (* predicateはboolean以外を返すことは無い。arithmeticの中にhfl predicateは現れない *)
  go hfl
  
let replace_mu_var_occurences : [`Int] Id.t -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t -> 'ty Hflz.t =
  fun var_y hfl sub_var -> 
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var sub_var, Arith (Op (Sub, [Var var_y; Int 1]))) else Var id)
      hfl

let replace_nu_var_occurences : [`Int] Id.t -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t -> 'ty Hflz.t =
  fun var_y hfl sub_var -> 
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var id, Arith (Var var_y)) else Var id)
      hfl

let get_rule : 'ty Id.t -> 'ty hes -> 'ty hes_rule =
  fun id hes ->
    match List.find_opt (fun {var;_} -> Id.eq var id) hes with
    | None -> assert false
    | Some rule -> rule

let remove_vars not_apply_vars = List.filter (fun v -> not @@ List.exists (fun v' -> Id.eq v' (Id.remove_ty v)) @@ not_apply_vars)

let extract_abstraction phi not_apply_vars new_rule_name_base =
  let xs, phi' = decompose_abs phi in
  (* 型情報も入っている。 *)
  (* arithの中のfvも見ている *)
  let free_vars =
    fvs_with_type phi
    |> remove_vars not_apply_vars in
  (* show *)
  print_endline "not_apply";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") not_apply_vars;
  print_endline "freevars";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") free_vars;
  (* TODO: 順番正しい？ *)
  let arr_type = to_arrow_type (free_vars @ xs) in
  (* 一般にはAbsが連続するので、連続したAbsをまとめて切り出したい *)
  let new_rule_id = Id.gen ~name:(new_rule_name_base ^ "_sub" ^ string_of_int (Random.int 100)) arr_type in
  let new_rule = {
    var = new_rule_id;
    body = (to_abs' (free_vars @ xs) phi');
    fix = Fixpoint.Greatest } in
  let new_sub_formula = args_ids_to_apps free_vars @@ Var new_rule_id in
  (new_sub_formula, new_rule)

let in_forall v =
  let rec forall_vars phi acc = match phi with
    | Forall (x, phi') -> forall_vars phi' (x::acc)
    | _ -> acc, phi in
  let rec abs_vars phi acc = match phi with
    | Abs (x, phi') -> abs_vars phi' (x::acc)
    | _ -> acc, phi in
  let fvars, v = forall_vars v [] in
  let avars, v = abs_vars v [] in
  to_abs' avars (to_forall fvars v)  
  
(* phiの中のlambdaをdecomposeする *)
let decompose_lambda_ (phi : Type.simple_ty Hflz.t) (rule_id : Type.simple_ty Id.t) (hes : Type.simple_ty hes) =
  let hes_var_names = List.map (fun {var; _} -> Id.remove_ty var) hes in
  let new_rules = ref [] in
  let rec go phi = match phi with
    | Var _ | Bool _ | Arith _ |  Pred _ -> phi
    | Or (phi1,phi2) -> Or(go phi1, go phi2)
    | And(phi1,phi2) -> And(go phi1, go phi2)
    | App(phi1,phi2) -> App(go phi1, go phi2)
    | Abs(_, _)    -> begin
      let v, new_rule = extract_abstraction phi ((Id.remove_ty rule_id)::hes_var_names) rule_id.name in
      new_rules := new_rule :: !new_rules;
      Log.app begin fun m -> m ~header:("Abs") "%a"
        Print.(hflz simple_ty_) v
      end;
      v
    end
    | Forall (x, phi) -> begin
      (* TODO: 直下にlambdaがあるとき以外にも対応させる。 *)
      match phi with
      | Abs _ -> begin
        let v, new_rule = extract_abstraction phi (Id.remove_ty x :: (Id.remove_ty rule_id :: hes_var_names)) rule_id.name in
        Log.app begin fun m -> m ~header:("Forall 前" ^ x.name) "%a"
          Print.(hflz simple_ty_) new_rule.body
        end;
        let new_rule = { new_rule with body = in_forall @@ Forall (x, new_rule.body) } in
        Log.app begin fun m -> m ~header:("Forall 後" ^ x.name) "%a"
          Print.(hflz simple_ty_) new_rule.body
        end;
        new_rules := new_rule :: !new_rules;
        v
      end
      | _ -> Forall(x, go phi)
    end
    (* TODO: *)
    | Exists _ -> failwith "not implemeneted"
  in
  (* 先頭のAbstractionとforallは読み飛ばす *)
  let rec go' phi = match phi with
    | Abs(x, phi) -> begin
      Abs(x, go' phi)
    end
    | _ -> go phi
  in
  Log.app begin fun m -> m ~header:"original formula" "%a"
    Print.(hflz simple_ty_) phi
  end;
  let res = go' phi in
  Log.app begin fun m -> m ~header:"converted formula" "%a"
    Print.(hflz simple_ty_) res
  end;
  Log.app begin fun m -> m ~header:"added_rules" "%a"
    Print.(hflz_hes simple_ty_) !new_rules
  end;
  (!new_rules, res)

(* abstractionをHESのequationに切り出す。 *)
(* これは、単一のruleに関するものである。 *)
let decompose_lambdas hes (rule : Type.simple_ty hes_rule) = 
  let rec go ({body; var; _} as rule) = 
    let new_rules, res = decompose_lambda_ body var hes in
    match new_rules with
    | [] -> [{rule with body = res}]
    | xs -> begin
      let xs = List.map (fun r -> go r) xs in
      {rule with body = res} :: List.flatten xs
    end in
  go rule

let decompose_lambdas_hes hes =
  hes |> List.map (decompose_lambdas hes) |> List.flatten

let move_first f ls =
  let l1, l2 = List.partition f ls in
  l1 @ l2

let elim_mu_with_rec (coe1 : int) (coe2 : int) (hes : Type.simple_ty Hflz.hes) : Type.simple_ty Hflz.hes =
  Log.app begin fun m -> m ~header:"AA11" "%a"
    Print.(hflz_hes simple_ty_) hes
  end;
  (* calc outer_mu_funcs *)
  (* これが何をやっているのか不明。hesはトップレベルの述語の情報は別途持っていて、それ以外は参照グラフから再構成する必要があるということ？listだから、順番の情報はあると思うが *)
  (* let outer_mu_funcs = get_outer_mu_funcs funcs in *)
  (* make tvars *)
  (*  *)
  type_check hes;
  if List.length hes = 0 then failwith "EMPTY HES";
  let {var=original_top_level_predicate;_} = List.nth hes 0 in
  let rec go : Type.simple_ty Hflz.hes -> Type.simple_ty Hflz.hes = fun hes -> 
    (* 最下層のmuを取得 *)
    (* どっちが下（内側）のレベルなのか？ *)
    let rem_level, mu_level, nu_level = get_next_mu_level hes in
    Log.app begin fun m -> m ~header:"nu_level" "%a"
      Print.(hflz_hes simple_ty_) nu_level
    end;
    Log.app begin fun m -> m ~header:"mu_level" "%a"
      Print.(hflz_hes simple_ty_) mu_level
    end;
    Log.app begin fun m -> m ~header:"rem_level" "%a"
      Print.(hflz_hes simple_ty_) rem_level
    end;
    let make_rec_var name = Id.gen ~name:("rec_" ^ name) `Int in
    match mu_level with
    | [] -> hes
    | _ -> 
      let mu_vars = mu_level
        |> List.map (fun ({var; _} as level) ->
          let rec_var = make_rec_var var.Id.name in
          (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)})) in
      let nu_vars = nu_level
        |> List.map (fun ({var; _} as level) ->
          let rec_var = make_rec_var var.Id.name in
          (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)})) in
      print_string @@ "len=" ^ string_of_int @@ List.length nu_vars;
      (* 置換 *)
      let new_level = (mu_vars @ nu_vars) |> List.map (fun ({body; fix; _}, rec_var, var) ->
        let head_abstacts, body = extract_head_abstracts body in
        (* 型: `IntはFormulaの中で使われる（Predの型で規定）、TypIntは述語の型で使う *)
        (* TODO: 名前の生成方法はこれでいいか確認 *)
        let body = mu_vars
          |> List.fold_left (fun body (_, _, mu_var) -> replace_mu_var_occurences rec_var body mu_var) body in
        let body = nu_vars
          |> List.fold_left (fun body (_, _, nu_var) -> replace_nu_var_occurences rec_var body nu_var) body in
        let body =
          head_abstacts @@ match fix with
          | Fixpoint.Least -> 
            And (Pred (Formula.Ge, [Var rec_var; Int 0]), body)
          | Fixpoint.Greatest ->
            body in
        let body = Abs ({rec_var with ty=TyInt}, body) in
        {var; body; fix=Fixpoint.Greatest}
      ) in
      let rem_level = rem_level |> List.map (fun ({body; _} as rule) -> 
        (* TODO: replace_callerにhesを渡さなくて本当に良いのか？ *)
        let body = replace_caller body (List.map (fun (_, _, v) -> v) @@ nu_vars @ mu_vars) coe1 coe2 in
        {rule with body = body}
      ) in
      (go rem_level) @ new_level in
  let hes = go hes in
  let hes = decompose_lambdas_hes hes in
  (* TODO: 場合によっては、TOP levelを上に持ってくることが必要になる？ *)
    (* |> move_first (fun {var; _} -> var.name = original_top_level_predicate.name) in *)
  Log.app begin fun m -> m ~header:"AA2" "%a"
    Print.(hflz_hes simple_ty_) hes
  end;
  type_check hes;
  hes

let flip_fixpoint = function
  | Fixpoint.Greatest -> Fixpoint.Least
  | Fixpoint.Least -> Fixpoint.Greatest

let negate_pred = function
  | Formula.Eq  -> Formula.Neq
  | Formula.Neq -> Formula.Eq
  | Formula.Le  -> Formula.Gt
  | Formula.Ge  -> Formula.Lt
  | Formula.Lt  -> Formula.Ge
  | Formula.Gt  -> Formula.Le
  
(* 追加すると非常に面倒。しかし、froallは必ず処理が必要。追加しないということはできない *)
(* negationをどう扱うか。基本的には、HFLにnegationは存在しないので、適宜なんとかする。 *)
let negate_formula (formula : Type.simple_ty Hflz.t) = 
  let rec go formula = match formula with
    | Bool b -> Bool (not b)
    | Var x  -> Var x
    | Or  (f1, f2) -> And (go f1, go f2)
    | And (f1, f2) -> Or  (go f1, go f2)
    | Abs (x, f1)  -> Abs (x, go f1)
    (* failwith "[negate_formula] Abs" *)
    | App (f1, f2) -> App (go f1, go f2)
    | Forall (x, f) -> Exists (x, go f)
    | Exists (x, f) -> Forall (x, go f)
    | Arith (arith) -> Arith (arith)
    | Pred (p, args) -> Pred (negate_pred p, args) in
  go formula

let negate_rule ({var; body; fix} : Type.simple_ty hes_rule) = 
  {var; body=negate_formula body; fix=flip_fixpoint fix}

let get_top_rule hes =
  match hes with
  | []  -> failwith "empty"
  | [x] -> x, []
  | x::xs -> begin
    match x with
    | { var=({ty=Type.TyBool ();_} as var); body; fix=Fixpoint.Greatest } -> begin
      let fvs = fvs_with_type body in
      match List.find_opt (fun fv -> Id.eq fv var) fvs with
      | None -> x, xs
      | Some _ -> failwith "not implemented"
    end
    | _ -> failwith "not implemented"
  end

let get_dual_hes (hes : Type.simple_ty hes) = 
  let top, others = get_top_rule hes in
  let results = List.map (fun rule -> negate_rule rule) others in
  { top with body = negate_formula top.body } :: results

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
  
let get_hflz_type phi =
  let rec go phi = match phi with
    | Hflz.Bool   _ -> Type.TyBool ()
    | Hflz.Var    v -> v.ty
    | Hflz.Or (f1, f2)  -> begin
      assert ((go f1) = Type.TyBool ());
      assert ((go f2) = Type.TyBool ());
      Type.TyBool ()
    end
    | Hflz.And (f1, f2) -> begin
      assert ((go f1) = Type.TyBool ());
      assert ((go f2) = Type.TyBool ());
      Type.TyBool ()
    end
    | Hflz.Abs (x, f1)  -> Type.TyArrow (x, go f1)
    | Hflz.Forall (x, f1) -> Type.TyArrow (x, go f1)
    | Hflz.Exists (x, f1) -> Type.TyArrow (x, go f1)
    | Hflz.App (f1, f2)   -> begin
      let ty1 = go f1 in
      match ty1 with
      | TyArrow (x, ty1') -> begin
        (match x.ty with
        | Type.TyInt -> (match f2 with Hflz.Arith _ -> () | _ -> failwith "illegal type")
        | Type.TySigma t -> assert (t = go f2)
        );
        ty1'
      end
      | _ -> failwith "illegal type"
      
    end
    | Hflz.Pred (p, args) -> Type.TyBool ()
    | Hflz.Arith t -> failwith "illegal"
  in
  go phi

let var_as_arith v = {v with Id.ty=`Int}

(* 特に変換の条件について、前提は無いはず *)
(* NOTE: 中から処理しないと、倍々に式が増幅される？。 *)
(* 式の内部に含まれているexistentialをforallを使った形に直す。lambdaはそのまま残る *)
let encode_body_exists_formula_sub coe1 coe2 env original_formula =
  match original_formula with
  | Hflz.Exists (fa_var, original_formula) -> begin
    (* 展開回数のための変数yは、existsされている変数をそのまま利用する。 *)
    let formula_type = get_hflz_type original_formula in
    (* 新たに作る述語 *)
    let fa_pred = Id.gen @@ Type.TyArrow (fa_var, formula_type) in
    let abs = to_abs @@ to_args @@ formula_type in
    let vars = to_vars (abs @@ Bool true) in
    (* TODO: forallの変数をどうするか確認 *)
    (* TODO: 高階変数を確認 *)
    (* 定数項があるので、 filter_int_variable した後の数は1以上であること は保証される *)
    let approx_formula =
      formula_type
      |> to_args
      |> filter_int_variable 
      |> make_bounds coe1 coe2
      |> make_approx_formula @@ var_as_arith fa_var in
    let free_vars =
      fvs_with_type original_formula 
      |> remove_vars (fa_var::env) in 
    let replaced_formula =  
      Forall (
        fa_var,
        abs @@ Or (
          approx_formula,
          vars @@
            args_ids_to_apps free_vars @@
            App (Var fa_pred, Arith (Var (var_as_arith fa_var)))
          )
        ) in
    let new_rule = {
      var=fa_pred;
      fix=Fixpoint.Greatest;
      body=(
        let subst_body =
          subst_arith_var
            (fun vid -> if vid = var_as_arith fa_var then (Arith.Op (Sub, [Int 0; Var (var_as_arith fa_var)])) else Var vid)
            original_formula in
        let body =
          And (
            Pred (Ge, [Var (var_as_arith fa_var); Int 0]),
            Or (
              vars @@ original_formula,
              Or(
                vars @@ subst_body,
                vars @@ (
                  App (
                    Var fa_pred,
                    Arith (Op (Sub, [Var (var_as_arith fa_var); Int 1]))
                  )
                )
              )
            )
          ) in
        let body = Abs(fa_var, to_abs' free_vars @@ abs @@ body) in
        body
      )
    } in
    replaced_formula, new_rule
  end
  | _ -> failwith "illegal"

let print_arg_type (arg_type : Type.simple_ty Type.arg) = 
  let go arg_type = match arg_type with
    | Type.TyInt -> print_string "int"
    | Type.TySigma ty -> Hflmc2_syntax.Print.simple_ty Format.std_formatter (ty);
  in
  go arg_type;
  print_endline ""

let encode_body_exists_formula coe1 coe2 env hfl =
  let new_rules = ref [] in
  let rec go env hfl = match hfl with
    | Var _ -> hfl
    | Bool _ -> hfl
    | Or (f1, f2)  -> Or  (go env f1, go env f2)
    | And (f1, f2) -> And (go env f1, go env f2)
    | Abs (v, f1)  -> Abs (v, go (v::env) f1)
    | Forall (v, f1) -> Forall (v, go ((v)::env) f1)
    | Exists (v, f1) -> begin
      if v.ty <> Type.TyInt then failwith "not implemented";
      (* print_endline "encode_body_exists_formula";
      print_endline @@ "var=" ^ v.name;
      print_arg_type v.ty; *)
      let f1 = go ((v)::env) f1 in
      let hfl, rule = encode_body_exists_formula_sub coe1 coe2 env hfl in
      new_rules := rule::!new_rules;
      hfl
    end
    | App (f1, f2) -> App (go env f1, go env f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t) in
  let hfl = go env hfl in
  hfl, !new_rules

(* hesからexistentailを除去 *)
let encode_body_exists coe1 coe2 (hes : Type.simple_ty Hflz.hes) =
  let env = List.map (fun {var; _} -> { var with ty=Type.TySigma var.ty }) hes in
  hes |>
  List.map
    (fun {var; fix; body} -> 
      let body, new_rules = encode_body_exists_formula coe1 coe2 env body in
      {var; fix; body}::new_rules
    )
  |> List.flatten
  |> decompose_lambdas_hes
