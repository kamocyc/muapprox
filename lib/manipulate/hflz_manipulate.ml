module Print = Print_syntax
module Fixpoint = Hflmc2_syntax.Fixpoint
module Formula = Hflmc2_syntax.Formula
module IdSet = Hflmc2_syntax.IdSet

open Hflz_typecheck
open Hflz
module Util = Hflmc2_util

let log_src = Logs.Src.create "Solver"
module Log = (val Logs.src_log @@ log_src)

let id_n n t = { Id.name = "x_" ^ string_of_int n; id = n; ty = t }
let show_hflz = Util.fmt_string (Print_syntax.hflz Print.simple_ty_)
let show_hflz_full v = Hflz.show (fun fmt ty_ -> Type.pp_simple_ty fmt ty_) v

let%expect_test "desugar_formula" =
  let open Type in
  let sugar : simple_ty Hflz.Sugar.t =
    (* true && (not (true && ∀x2. 1 >= x2 || ∃x3. not (true && x4 5))) *)
    (* => *)
    (* true && (false || ∃x2. 1 < x2 && ∀x3. true && x4 5) *)
    And (Bool true, Not (And (Bool true, Forall (id_n 2 TyInt, Or (Pred (Ge, [Int 1; Var (id_n 2 `Int)]), Exists (id_n 3 TyInt, Not (And (Bool true, App (Var (id_n 4 (TyBool ())), Arith (Int 5)))))))))) in
  let desugar = Hflz.desugar_formula sugar in
  ignore [%expect.output];
  print_endline @@ show_hflz desugar;
  [%expect {| true && (false || (∃x_22.1 < x_22 && (∀x_33.true && (x_44 :bool) 5))) |}]

(* Arrow type to list of types of the arguments conversion *)
(* t1 -> t2 -> t3  ==> [t3; t2; t1]  *)
let to_args : Type.simple_ty -> Type.simple_ty Type.arg Id.t list =
  let rec go =
    fun acc ty -> match ty with
    | Type.TyArrow (arg, ty) -> go (arg::acc) ty
    | Type.TyBool _ -> acc in
  go []

let%expect_test "to_args" =
  let open Type in
  let res = to_args @@ TyArrow (id_n 1 TyInt, TyArrow (id_n 2 TyInt, TyArrow (id_n 3 (TySigma (TyBool ())), TyBool ()))) in
  ignore [%expect.output];
  Util.print_list (Id.show (fun fmt ty_ -> pp_simple_argty fmt ty_)) res;
  [%expect {|
    [ { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] |}]

(* 引数のリストからabstractionに変換。IDは新規に生成する。 *)
let to_abs : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) = fun args ->
  let name_map = List.map (fun arg -> (arg.Id.name, Id.gen ~name:arg.Id.name arg.Id.ty)) args in
  fun body -> 
    let rec go = function
      | [] -> body
      | arg::xs -> Abs (List.assoc arg.Id.name name_map, go xs) in
    go args

let%expect_test "to_abs" =
  let open Type in
  let res = to_abs [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_3"; id = 0; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 1; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 2; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]

(* Absの引数のIDを新規に生成しない版 *)
(* [x1; x2] body  ->  \x1. \x2. body *)
let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args

let%expect_test "to_abs'" =
  let open Type in
  let res = to_abs' [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]
    
let to_forall args body =
  let rec go = function
    | [] -> body
    | arg::xs -> Forall(arg, go xs) in
  go args
  
let%expect_test "to_forall" =
  let res = to_forall [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Forall (
       { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Forall ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Forall ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]

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

let%expect_test "to_vars" =
  let open Type in
  let res =
    to_vars
      (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) (Bool false) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.App (
       (Hflz.App (
          (Hflz.App ((Hflz.Bool false),
             (Hflz.Arith (Arith.Var { Id.name = "x_1"; id = 1; ty = `Int })))),
          (Hflz.Arith (Arith.Var { Id.name = "x_2"; id = 2; ty = `Int })))),
       (Hflz.Var { Id.name = "x_3"; id = 3; ty = (Type.TyBool ()) }))) |}] 
     
let make_guessed_terms (coe1 : int) (coe2 : int) vars =
  let mk_affine term coe1 coe2 = Arith.Op (Arith.Add, [Arith.Op (Mult, [Int coe1; term]); Int coe2]) in
  match vars |>
    List.map (fun var -> mk_affine (Var var) coe1 coe2 :: [mk_affine (Var var) (-coe1) coe2]) |>
    List.flatten with
  | [] -> [Arith.Int coe2]
  | vars -> vars

let%expect_test "make_guessed_terms" =
  let res = make_guessed_terms 2 10 [id_n 1 `Int; id_n 2 `Int] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|
    [ 2 * x_11 + 10;
    -2 * x_11 + 10;
    2 * x_22 + 10;
    -2 * x_22 + 10 ] |}];
  let res = make_guessed_terms 2 10 [] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|[ 10 ]|}]
     
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

let%expect_test "rev_abs" =
  let res =
    rev_abs
      (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
        (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
              (Hflz.Bool true)))
          ))
        )) in
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs (
             { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
             (Hflz.Bool true)))
          ))
       )) |}]
  

(* 環境は、近似式を作るためだけに使う *)
(* 引数は近似回数用の変数の1つぶんだけ増える *)
let replace_caller_sub coe1 coe2 env id id' =
  (* 処理対象のpredicateであるとき *)
  let new_rec_var = Id.gen ~name:"forall_y" Type.TyInt in
  let new_rec_var_f = {new_rec_var with ty = `Int} in
  (* predicateの型から引数を取得 *)
  (* TODO: predicateが部分適用されているとき *)
  (* negativeにしているので注意 *)
  let approx_formula =
    let bound_int_vars = filter_int_variable env in
    let guessed_terms = make_guessed_terms coe1 coe2 bound_int_vars in
    make_approx_formula new_rec_var_f guessed_terms in
  let abs = to_abs (List.rev @@ to_args id'.Id.ty) in
  let vars = to_vars (rev_abs (abs @@ (* Dummy *) Bool true)) in
  Forall (new_rec_var, abs @@ Or (approx_formula, vars @@ App (Var id, Arith (Var new_rec_var_f))))

let%expect_test "replace_caller_sub" =
  let open Type in
  let res =
    replace_caller_sub
      1
      10
      [
        id_n 1 TyInt;
        id_n 2 (TySigma (TyBool ()));
        id_n 3 (TySigma (TyArrow (id_n 4 TyInt, TyBool ())));
        id_n 5 TyInt] (* env *)
      (id_n 11 (TyArrow (id_n 12 TyInt, TyArrow (id_n 13 (TySigma (TyBool ())), TyArrow (id_n 14 (TySigma (TyArrow (id_n 15 TyInt, TyBool ()))), TyBool ())))))
      (id_n 21 (                        TyArrow (id_n 13 (TySigma (TyBool ())), TyArrow (id_n 14 (TySigma (TyArrow (id_n 15 TyInt, TyBool ()))), TyBool ()))))
      in
  ignore [%expect.output];
  print_endline @@ show_hflz res;
  [%expect {|
    ∀forall_y3.
     λx_134:bool.
      λx_145:(int -> bool).
       forall_y3 < 1 * x_11 + 10 || forall_y3 < -1 * x_11 + 10
       || forall_y3 < 1 * x_55 + 10
       || forall_y3 < -1 * x_55 + 10
       || (x_1111 :int -> bool -> (int -> bool) -> bool) forall_y3 (x_134 :bool)
           (x_145 :int -> bool) |}]

(* 変換した述語の呼び出し元を置換 *)
let replace_caller (hfl : Type.simple_ty Hflz.t) (preds : Type.simple_ty Id.t list) (coe1 : int) (coe2 : int) : Type.simple_ty Hflz.t =
  let rec go env (hfl : Type.simple_ty Hflz.t) : Type.simple_ty Hflz.t = match hfl with
    | Var id' -> begin
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
    (* print_endline "replace_mu_var_occurences";
    print_endline @@ Id.to_string sub_var;
    print_endline @@ fmt_string Print.simple_ty sub_var.ty;
    print_endline ""; *)
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var sub_var, Arith (Op (Sub, [Var var_y; Int 1]))) else Var id)
      hfl

let replace_nu_var_occurences : [`Int] Id.t -> Type.simple_ty Hflz.t -> Type.simple_ty Id.t -> 'ty Hflz.t =
  fun var_y hfl sub_var -> 
    (* print_endline "replace_nu_var_occurences";
    print_endline @@ Id.to_string sub_var;
    print_endline @@ fmt_string Print.simple_ty sub_var.ty;
    print_endline ""; *)
    replace_var_occurences
      (fun id -> if Id.eq id sub_var then App (Var sub_var, Arith (Var var_y)) else Var id)
      hfl

let get_rule : 'ty Id.t -> 'ty hes -> 'ty hes_rule =
  fun id hes ->
    match List.find_opt (fun {var;_} -> Id.eq var id) hes with
    | None -> assert false
    | Some rule -> rule

let extract_abstraction phi not_apply_vars new_rule_name_base =
  let xs, phi' = decompose_abs phi in
  print_endline "extract_abstraction";
  List.iter (fun x -> print_endline @@ Id.to_string x) xs;
  (* 型情報も入っている。 *)
  (* arithの中のfvも見ている *)
  let free_vars =
    Hflz.fvs_with_type phi
    |> Id.remove_vars not_apply_vars in
  (* show *)
  print_endline "not_apply";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") not_apply_vars;
  print_endline "freevars";
  List.iter (fun v -> print_string v.Id.name; print_int v.Id.id; print_string ";") free_vars;
  (* TODO: 順番正しい？ *)
  let arr_type = to_arrow_type (free_vars @ xs) in
  let new_rule_id = Id.gen ~name:(new_rule_name_base ^ "_sub" ^ string_of_int (Id.gen_id ())) arr_type in
  let new_rule = {
    var = new_rule_id;
    body = (to_abs' (free_vars @ xs) phi');
    fix = Fixpoint.Greatest } in
  print_endline "NEW_RULE";  
  print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_ ) new_rule;
  let new_sub_formula = args_ids_to_apps free_vars @@ Var new_rule_id in
  (new_sub_formula, new_rule)

let%expect_test "extract_abstraction" =
  let open Type in
  let open Arith in
  let (f, rule) =
    extract_abstraction
      (Abs (id_n 1 (TyInt), Abs (id_n 2 (TySigma (TyBool ())),
        App (Var (id_n 4 (TyArrow (id_n 5 TyInt, TyBool ()))), Arith (Op (Add, [Var (id_n 1 `Int); Op (Mult, [Var (id_n 2 `Int); Var (id_n 3 `Int)])])))
      )))
      [(id_n 4 (TyArrow (id_n 5 TyInt, TyBool ())))]
      "a" in
  ignore [%expect.output];
  print_endline @@ show_hflz f;
  print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_) rule;
  [%expect {|
    (a_sub67 :int -> int -> bool -> bool) x_33
    a_sub67 : int -> int -> bool -> bool =ν
      λx_33:int.λx_11:int.λx_22:bool.(x_44 :int -> bool) (x_11 + x_22 * x_33) |}]

(* (∀x1. ∀x2. \y1. \y2. \phi)  ->  (\y1. \y2. ∀x1. ∀x2. \phi) *)
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

let%expect_test "in_forall" =
  let open Type in
  let open Arith in
  let v =
    in_forall
      (Forall (id_n 3 TyInt, Forall (id_n 4 (TySigma (TyBool ())), Abs (id_n 1 (TyInt), Abs (id_n 2 (TySigma (TyBool ())), Bool true))))) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full v;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
       (Hflz.Abs (
          { Id.name = "x_2"; id = 2; ty = (Type.TySigma (Type.TyBool ())) },
          (Hflz.Forall ({ Id.name = "x_3"; id = 3; ty = Type.TyInt },
             (Hflz.Forall (
                { Id.name = "x_4"; id = 4; ty = (Type.TySigma (Type.TyBool ())) },
                (Hflz.Bool true)))
             ))
          ))
       )) |}]
      
type forall_or_exists =
  | FE_Forall of Type.simple_ty Type.arg Id.t
  | FE_Exists of Type.simple_ty Type.arg Id.t

(* phiの中のlambdaをdecomposeする *)
let decompose_lambda_ (phi : Type.simple_ty Hflz.t) (rule_id : Type.simple_ty Id.t) (hes : Type.simple_ty hes) =
  let hes_var_names = List.map (fun {var; _} -> Id.remove_ty var) hes in
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

let elim_mu_with_rec (coe1 : int) (coe2 : int) (hes : Type.simple_ty Hflz.hes) : Type.simple_ty Hflz.hes =
  Log.app begin fun m -> m ~header:"FIRST" "%a" Print.(hflz_hes simple_ty_) hes end;
  (* calc outer_mu_funcs *)
  (* これが何をやっているのか不明。hesはトップレベルの述語の情報は別途持っていて、それ以外は参照グラフから再構成する必要があるということ？listだから、順番の情報はあると思うが *)
  (* let outer_mu_funcs = get_outer_mu_funcs funcs in make tvars *)
  type_check hes;
  if List.length hes = 0 then failwith "EMPTY HES";
  (* let {var=original_top_level_predicate;_} = List.nth hes 0 in *)
  let extract_var ({var; _} as level) =
    let rec_var = Id.gen ~name:("rec_" ^ var.Id.name) `Int in
    (level, rec_var, {var with Id.ty=Type.TyArrow({rec_var with ty=TyInt}, var.Id.ty)}) in
  let rec go (hes : Type.simple_ty Hflz.hes) : Type.simple_ty Hflz.hes =
    (* 最下層のmuを取得 *)
    let rem_level, mu_level, nu_level = get_next_mu_level hes in
    Log.app begin fun m -> m ~header:"nu_level" "%a" Print.(hflz_hes simple_ty_)  nu_level  end;
    Log.app begin fun m -> m ~header:"mu_level" "%a" Print.(hflz_hes simple_ty_)  mu_level  end;
    Log.app begin fun m -> m ~header:"rem_level" "%a" Print.(hflz_hes simple_ty_) rem_level end;
    match mu_level with
    | [] -> hes (* finish *)
    | _ -> begin
      let mu_vars = List.map extract_var mu_level in
      let nu_vars = List.map extract_var nu_level in
      (* print_string @@ "len=" ^ string_of_int @@ List.length nu_vars; *)
      (* 置換 *)
      let new_level = (mu_vars @ nu_vars) |> List.map (fun ({body; fix; _}, rec_var, var) -> begin
        let head_abstacts, body = extract_head_abstracts body in
        (* 型: `IntはFormulaの中で使われる（Predの型で規定）、TypIntは述語の型で使う *)
        (* TODO: 名前の生成方法はこれでいいか確認 *)
        let body = mu_vars |> List.fold_left (fun body (_, _, mu_var) -> replace_mu_var_occurences rec_var body mu_var) body in
        let body = nu_vars |> List.fold_left (fun body (_, _, nu_var) -> replace_nu_var_occurences rec_var body nu_var) body in
        let body =
          head_abstacts @@ match fix with
          | Fixpoint.Least    -> And (Pred (Formula.Ge, [Var rec_var; Int 0]), body)
          | Fixpoint.Greatest -> body in
        let body = Abs ({rec_var with ty=TyInt}, body) in
        {var; body; fix=Fixpoint.Greatest}
      end) in
      let mu_nu_var_ids = List.map (fun (_, _, v) -> v) (nu_vars @ mu_vars) in
      let rem_level = rem_level |> List.map (fun rule -> {rule with body = replace_caller rule.body mu_nu_var_ids coe1 coe2}) in
      go (rem_level @ new_level)
    end in
  let hes = go hes in
  let path = Print_syntax.MachineReadable.save_hes_to_file true hes in
  print_endline @@ "Not decomposed HES path: " ^ path;
  let hes = decompose_lambdas_hes hes in
  (* TODO: 場合によっては、TOP levelを上に持ってくることが必要になる？ *)
    (* |> move_first (fun {var; _} -> var.name = original_top_level_predicate.name) in *)
  Log.app begin fun m -> m ~header:"FINAL" "%a"
    Print.(hflz_hes simple_ty_) hes
  end;
  type_check hes;
  hes
  
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
      | Some _ -> failwith "not implemented"
    end
    | _ -> failwith "not implemented"
  end

let get_dual_hes (hes : Type.simple_ty hes) = 
  let top, others = get_top_rule hes in
  let results = List.map (fun rule -> Hflz.negate_rule rule) others in
  let results = { top with body = Hflz.negate_formula top.body } :: results in
  Log.app begin fun m -> m ~header:"get_dual_hes" "%a" Print.(hflz_hes simple_ty_) results end;
  type_check results;
  results

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
  
(* let () =
  let open Type in
  let rec go vars = match vars with
    | [] -> TyBool ()
    | x::xs -> TyArrow (x, go xs) in
  rep  *)
  
(* 高階だからちょっと変わる *)
let encode_body_exists_formula_sub coe1 coe2 separate_original_formula hes_preds hfl = 
  let open Type in
  if separate_original_formula then failwith "encode_body_exists_formula_sub: not implemented";
  (* let formula_type_abs = formula_type |> to_args |> to_abs in *)
  let formula_type_vars = Hflz.get_hflz_type hfl |> to_args |> List.rev in
  (* print_endline @@ Util.fmt_string Print.simple_ty formula_type; *)
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
    List.sort (fun a b -> Int.compare a.Id.id b.Id.id) |>
    List.filter_map (fun var -> 
      match var.Id.ty with
      | TyInt ->
        (* Some (Id.gen ~name:("exi_" ^ var.name) TyInt) *)
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
  (* let bound_vars_argty = bound_vars |> List.map (fun v -> { v with Id.ty=TyInt}) in *)
  let new_pvar =
    let i = Id.gen_id() in
    let ty =
      (* TODO: higher-order vars *)
      to_tree
        arg_vars
        (fun x rem -> TyArrow (x, rem))
        (TyBool ())  in
    { Id.name = "Exists" ^ string_of_int i; ty = ty; id = i } in
  let body =
    let guessed_terms = make_guessed_terms coe1 coe2 (free_vars |> filter_int_variable) in
    let approx_formulas = bound_vars |> List.map (fun bound_var -> make_approx_formula ({bound_var with ty=`Int}) guessed_terms) in
    to_tree
      bound_vars
      (fun x rem -> Forall (x, rem)) @@
      rev_abs (
        (formula_type_vars |> List.rev |> to_abs') @@
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
          bound_vars
          |> List.map (fun var -> Pred (Ge, [Var {var with ty=`Int}; Int 0]))
          |> formula_fold (fun acc f -> And (acc, f)),
          (* substitute rec vars to negative *)
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
          (terms1 @ terms2) |> formula_fold (fun acc f -> Or (acc, f))
        )
    }]    

let%expect_test "encode_body_exists_formula_sub" =
  let open Type in
  let p = id_n 10 (TySigma (TyArrow (id_n 12 TyInt, (TyArrow (id_n 11 TyInt, TyBool ()))))) in
  (* 高階変数の扱い *)
  (* その時点で使える自由変数ということは、直前のラムダ抽象も含まれる？ => いや、そこは使わない。あくまで式の中の型を取得するだけなので、別。free var のみを使用 *)
  (* ∃x_100.∃x_300.λx_1:int.λx_2:(int -> bool).(x_10 :int -> int -> bool) (x_1 + x_3) x_300 && (x_2:int -> bool) x_5 && (x_4:int -> bool) x_100 *)
  (* other predicates = x10 : int -> bool *)
  (* arguments in the term's type = x1 : int, x2 : int -> bool *)
  (* free variables = x3 : int, x4 : int -> bool, x5 : int *)
  let org_formula =
    Exists (id_n 100 TyInt, Exists (id_n 300 TyInt, Abs (id_n 1 TyInt, Abs (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))),
      And (
        App (App (Var { p with ty = unsafe_unlift p.ty }, 
          Arith (Op (Add, [Var (id_n 1 `Int); Var (id_n 3 `Int)]))), Arith (Var (id_n 300 `Int))),
        And (App (Var (id_n 2 (TyArrow (id_n 31 TyInt, TyBool ()))), Arith (Var (id_n 5 `Int))),
          App (Var (id_n 4 (TyArrow (id_n 32 TyInt, TyBool ()))), Arith (Var (id_n 100 `Int)))))
      )))) in
  print_endline @@ "original: " ^ show_hflz org_formula;
  [%expect {|
    original: ∃x_100100.
     ∃x_300300.
      λx_11:int.
       λx_22:(int -> bool).
        (x_1010 :int -> int -> bool) (x_11 + x_33) x_300300
        && (x_22 :int -> bool) x_55 && (x_44 :int -> bool) x_100100 |}];
  let (replaced, rules) =
    encode_body_exists_formula_sub
      1
      10
      false
      [p]
      org_formula
    in
  ignore [%expect.output];
  print_endline @@ string_of_int @@ List.length rules;
  let rule = List.nth rules 0 in
  print_endline @@ "replaced: " ^ show_hflz replaced;
  [%expect {|
    1
    replaced: ∀x_100100.
     ∀x_300300.
      λx_11:int.
       λx_22:(int -> bool).
        x_100100 < 1 * x_33 + 10 || x_100100 < -1 * x_33 + 10
        || x_100100 < 1 * x_55 + 10
        || x_100100 < -1 * x_55 + 10
        || x_300300 < 1 * x_33 + 10 || x_300300 < -1 * x_33 + 10
           || x_300300 < 1 * x_55 + 10
           || x_300300 < -1 * x_55 + 10
        || (Exists8 :int ->
                      (int -> bool) ->
                       int -> int -> (int -> bool) -> int -> int -> bool)
            x_33 (x_44 :int -> bool) x_55 x_11 (x_22 :int -> bool) x_100100
            x_300300 |}];
  print_endline @@ "fix: " ^ Fixpoint.show rule.fix;
  print_endline @@ "var: " ^ Id.show pp_simple_ty rule.var;
  print_endline @@ "rule: " ^ show_hflz rule.body;
  [%expect {|
    fix: Fixpoint.Greatest
    var: { Id.name = "Exists8"; id = 8;
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
           x_100100 >= 0 && x_300300 >= 0
           && ((λx_11:int.
                 λx_22:(int -> bool).
                  (x_1010 :int -> int -> bool) (x_11 + x_33) x_300300
                  && (x_22 :int -> bool) x_55 && (x_44 :int -> bool) x_100100)
                x_11 (x_22 :int -> bool)
               || (λx_11:int.
                    λx_22:(int -> bool).
                     (x_1010 :int -> int -> bool) (x_11 + x_33) (-x_300300)
                     && (x_22 :int -> bool) x_55 && (x_44 :int -> bool) x_100100)
                   x_11 (x_22 :int -> bool)
               || (λx_11:int.
                    λx_22:(int -> bool).
                     (x_1010 :int -> int -> bool) (x_11 + x_33) x_300300
                     && (x_22 :int -> bool) x_55
                        && (x_44 :int -> bool) (-x_100100))
                   x_11 (x_22 :int -> bool)
               || (λx_11:int.
                    λx_22:(int -> bool).
                     (x_1010 :int -> int -> bool) (x_11 + x_33) (-x_300300)
                     && (x_22 :int -> bool) x_55
                        && (x_44 :int -> bool) (-x_100100))
                   x_11 (x_22 :int -> bool)
               || (Exists8 :int ->
                             (int -> bool) ->
                              int -> int -> (int -> bool) -> int -> int -> bool)
                   x_33 (x_44 :int -> bool) x_55 x_11 (x_22 :int -> bool)
                   (x_100100 - 1) x_300300
               || (Exists8 :int ->
                             (int -> bool) ->
                              int -> int -> (int -> bool) -> int -> int -> bool)
                   x_33 (x_44 :int -> bool) x_55 x_11 (x_22 :int -> bool)
                   x_100100 (x_300300 - 1)) |}];
  (* check well-typedness *)
  let hes = [
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
  let hes = decompose_lambdas_hes hes in
  type_check hes;
  ignore [%expect.output];
  print_endline "OK";
  [%expect {|OK|}]

let encode_body_exists_formula coe1 coe2 (separate_original_formula : bool) hes_preds hfl =
  Log.app begin fun m -> m ~header:"encode_body_exists_formula (ORIGINAL)" "%a" Print.(hflz simple_ty_) hfl end;
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
        | Some x -> failwith "quantifiers for higher-order variables are not implemented"
      ) else (
        print_endline "encode_body_exists_formula";
        print_endline @@ "var=" ^ v.name;
        Print_syntax.print_arg_type v.ty;
        (* let f1 = go ((v)::env) f1 in *)
        let hfl, rules = encode_body_exists_formula_sub coe1 coe2 separate_original_formula hes_preds hfl in
        let new_rule_vars = List.map (fun rule -> { rule.var with ty = Type.TySigma rule.var.ty }) rules in
        let rules = List.map (fun rule -> { rule with body = go (new_rule_vars @ hes_preds) rule.body } ) rules in
        print_endline "HFLLL";
        print_endline @@ Util.fmt_string (Print.hflz Print.simple_ty_) hfl;
        Print_syntax.print_arg_type v.ty;
        new_rules := rules @ !new_rules;
        hfl
      )
    end
    | App (f1, f2) -> App (go hes_preds f1, go hes_preds f2)
    | Arith t -> Arith t
    | Pred (p, t) -> Pred (p, t) in
  let hfl = go hes_preds hfl in
  Log.app begin fun m -> m ~header:"encode_body_exists_formula" "%a" Print.(hflz simple_ty_) hfl end;
  Log.app begin fun m -> m ~header:"!new_rules" "%a" Print.(hflz_hes simple_ty_) (!new_rules) end;
  hfl, !new_rules

(* hesからexistentailを除去 *)
let encode_body_exists coe1 coe2 separate_original_formula (hes : Type.simple_ty Hflz.hes) =
  let env = List.map (fun {var; _} -> { var with ty=Type.TySigma var.ty }) hes in
  hes |>
  List.map
    (fun {var; fix; body} -> 
      let body, new_rules = encode_body_exists_formula coe1 coe2 separate_original_formula env body in
      {var; fix; body}::new_rules
    )
  |> List.flatten
  |> (fun hes -> 
    let path = Print_syntax.MachineReadable.save_hes_to_file true hes in
    print_endline @@ "Not decomposed HES path (Exists): " ^ path; hes)
  |> decompose_lambdas_hes
